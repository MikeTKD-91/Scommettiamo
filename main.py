from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, time, random
from datetime import datetime, timezone, timedelta
import json

app = Flask(__name__)
CORS(app)

# ── Database ───────────────────────────────────────────────────────────────────
DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "scommettiamo.db")
db_lock = threading.Lock()

def get_db():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with db_lock:
        conn = get_db()
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS team_stats (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                team_name TEXT NOT NULL,
                fd_code TEXT NOT NULL,
                season TEXT NOT NULL,
                att_h REAL, att_a REAL,
                def_h REAL, def_a REAL,
                wf_home REAL, wf_away REAL,
                home_advantage REAL,
                form TEXT,
                updated_at TEXT,
                UNIQUE(team_name, fd_code, season)
            );
            CREATE TABLE IF NOT EXISTS odds_cache (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                date TEXT NOT NULL,
                league_key TEXT NOT NULL,
                data TEXT NOT NULL,
                updated_at TEXT,
                UNIQUE(date, league_key)
            );
            CREATE TABLE IF NOT EXISTS job_log (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                job_name TEXT,
                status TEXT,
                message TEXT,
                ran_at TEXT
            );
        """)
        conn.commit()
        conn.close()

init_db()

# ── Config ─────────────────────────────────────────────────────────────────────
LEAGUE_AVG = 1.35

# Non più usato per The Odds API, lo teniamo per compatibilità fd_code
LEAGUES = []  # vuoto ora

TARGET_CONFIG = {
    3:   {"min_picks": 2, "max_picks": 3},
    5:   {"min_picks": 3, "max_picks": 4},
    8:   {"min_picks": 4, "max_picks": 5},
    10:  {"min_picks": 4, "max_picks": 6},
    100: {"min_picks": 6, "max_picks": 9},
}

def get_cfg(target):
    for k in sorted(TARGET_CONFIG.keys()):
        if target <= k: return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

# ── Poisson + Dixon-Coles ──────────────────────────────────────────────────────
def dc_tau(x, y, lh, la, rho=-0.13):
    if x == 0 and y == 0: return max(0.001, 1 - lh * la * rho)
    if x == 0 and y == 1: return max(0.001, 1 + lh * rho)
    if x == 1 and y == 0: return max(0.001, 1 + la * rho)
    if x == 1 and y == 1: return max(0.001, 1 - rho)
    return 1.0

def pmf(lam, k):
    if lam <= 0: return 0
    return math.exp(k * math.log(lam) - lam - sum(math.log(i) for i in range(1, k+1)))

def calc_probs(lh, la):
    o15 = o25 = gg = 0.0
    for h in range(9):
        for a in range(9):
            p = pmf(lh, h) * pmf(la, a) * dc_tau(h, a, lh, la)
            t = h + a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if h > 0 and a > 0: gg += p
    return {"over15": min(o15,.99), "over25": min(o25,.99), "gg": min(gg,.99)}

# ── Stats dal DB ───────────────────────────────────────────────────────────────
def get_stats_from_db(team_name, fd_code, season="2025"):
    if not fd_code: return None
    with db_lock:
        conn = get_db()
        row = conn.execute(
            "SELECT * FROM team_stats WHERE team_name=? AND fd_code=? AND season=?",
            (team_name, fd_code, season)
        ).fetchone()
        conn.close()
    if not row: return None
    return dict(row)

def save_stats_to_db(team_name, fd_code, season, stats):
    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO team_stats
            (team_name, fd_code, season, att_h, att_a, def_h, def_a, wf_home, wf_away, home_advantage, form, updated_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            team_name, fd_code, season,
            stats["att_h"], stats["att_a"],
            stats["def_h"], stats["def_a"],
            stats["wf_home"], stats["wf_away"],
            stats["home_advantage"], stats["form"],
            datetime.now(timezone.utc).isoformat()
        ))
        conn.commit()
        conn.close()

# ── football-data.org sync (opzionale, lo lasciamo) ────────────────────────────
# ... (tieni le funzioni fetch_team_stats_fd, sync_league_stats, weighted_form come prima)

# ── Lambda calc ────────────────────────────────────────────────────────────────
def calc_lambda(hs, as_):
    avg = LEAGUE_AVG
    if hs and as_:
        lh = avg * hs["att_h"] * as_["def_a"] * min(hs["home_advantage"], 1.4)
        la = avg * as_["att_a"] * hs["def_h"]
        lh *= 0.85 + hs["wf_home"] * 0.30
        la *= 0.85 + as_["wf_away"] * 0.30
    elif hs:
        lh = avg * hs["att_h"] * min(hs["home_advantage"], 1.3) * (0.85 + hs["wf_home"] * 0.30)
        la = avg * hs["def_h"]
    elif as_:
        lh = avg * as_["def_a"]
        la = avg * as_["att_a"] * (0.85 + as_["wf_away"] * 0.30)
    else:
        lh = la = avg
    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

def form_score(form):
    if not form: return 0.5
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in form[-5:]) / 15

# ── Sofascore fetch ────────────────────────────────────────────────────────────
SOFA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Referer": "https://www.sofascore.com/",
    "Accept": "*/*",
    "Accept-Language": "it-IT,it;q=0.9,en-US;q=0.8,en;q=0.7",
}

SOFA_CACHE_TTL = 3600 * 1  # 1 ora

def get_sofascore_cache(date_str):
    with db_lock:
        conn = get_db()
        row = conn.execute(
            "SELECT data, updated_at FROM odds_cache WHERE date=? AND league_key='sofascore'",
            (date_str,)
        ).fetchone()
        conn.close()
    if row:
        updated = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc) - updated).total_seconds() < SOFA_CACHE_TTL:
            return json.loads(row["data"])
    return None

def save_sofascore_cache(date_str, data):
    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO odds_cache (date, league_key, data, updated_at)
            VALUES (?,?,?,?)
        """, (date_str, "sofascore", json.dumps(data), datetime.now(timezone.utc).isoformat()))
        conn.commit()
        conn.close()

def fetch_sofascore_day(date_str, start_utc, end_utc):
    cached = get_sofascore_cache(date_str)
    if cached:
        return cached, True

    url = f"https://api.sofascore.com/api/v1/sport/football/scheduled-events/{date_str}"
    try:
        r = requests.get(url, headers=SOFA_HEADERS, timeout=12)
        if not r.ok:
            return [], False

        data = r.json()
        events = data.get("events", [])

        processed = []
        for ev in events:
            if ev.get("status", {}).get("type") not in ["scheduled"]:
                continue

            ts = ev.get("startTimestamp")
            if not ts:
                continue
            ev_time = datetime.fromtimestamp(ts, tz=timezone.utc)
            if not (start_utc <= ev_time <= end_utc):
                continue

            # Dettagli evento
            time.sleep(5 + random.uniform(0, 4))
            detail_url = f"https://api.sofascore.com/api/v1/event/{ev['id']}"
            rd = requests.get(detail_url, headers=SOFA_HEADERS, timeout=10)
            detail_data = rd.json() if rd.ok else {}

            # Odds (spesso in un endpoint separato)
            time.sleep(5 + random.uniform(0, 4))
            odds_url = f"https://api.sofascore.com/api/v1/event/{ev['id']}/odds/1/full"  # prova varianti: /all, /full, /average
            ro = requests.get(odds_url, headers=SOFA_HEADERS, timeout=10)
            odds_data = ro.json() if ro.ok else {}

            ev_copy = ev.copy()
            ev_copy["detail"] = detail_data.get("event", {})
            ev_copy["odds"] = odds_data
            processed.append(ev_copy)

        if processed:
            save_sofascore_cache(date_str, processed)
        return processed, False

    except Exception as e:
        print(f"Errore fetch Sofascore: {str(e)}")
        return [], False

# ── Nuova analyze per Sofascore ────────────────────────────────────────────────
def analyze_event_sofa(ev, dummy_league={"flag": "⚽", "name": "Sofascore"}):
    try:
        detail = ev.get("detail", {})
        home = detail.get("homeTeam", {}).get("name", "Home")
        away = detail.get("awayTeam", {}).get("name", "Away")
        commence_time = datetime.fromtimestamp(ev.get("startTimestamp", 0), tz=timezone.utc).isoformat()

        # Stats squadre (prova a prendere da detail se disponibili, altrimenti DB)
        hs = get_stats_from_db(home, None)   # fd_code None per Sofascore
        as_ = get_stats_from_db(away, None)
        lh, la = calc_lambda(hs, as_)
        pr = calc_probs(lh, la)
        hf = form_score(hs.get("form", "") if hs else "")
        af = form_score(as_.get("form", "") if as_ else "")
        exp_g = round(lh + la, 2)
        has_real = bool(hs or as_)

        picks = []

        # Parsing quote Sofascore - QUESTA PARTE VA ADATTATA guardando JSON reale!
        odds_data = ev.get("odds", {})
        markets = odds_data.get("markets", []) if isinstance(odds_data, dict) else []

        for m in markets:
            market_name = m.get("marketName", "").lower()
            choices = m.get("choices", [])

            if "over/under" in market_name:
                for ch in choices:
                    name_ch = ch.get("name", "").lower()
                    odds_val = float(ch.get("odds", 0))
                    point = ch.get("point", 0)

                    if point == 1.5 and "over" in name_ch and 1.05 <= odds_val <= 1.70:
                        prob = pr["over15"]
                        edge = prob - 1 / odds_val if odds_val > 0 else 0
                        picks.append({
                            "name": "Over 1.5",
                            "odds": round(odds_val, 2),
                            "prob": round(prob, 3),
                            "edge": round(edge, 3),
                            "market": "over15",
                            "probs": pr,
                            "exp_g": exp_g,
                            "home_form": round(hf,2),
                            "away_form": round(af,2),
                            "has_real_stats": has_real
                        })

                    if point == 2.5 and "over" in name_ch and 1.30 <= odds_val <= 2.70:
                        prob = pr["over25"]
                        edge = prob - 1 / odds_val if odds_val > 0 else 0
                        picks.append({
                            "name": "Over 2.5",
                            "odds": round(odds_val, 2),
                            "prob": round(prob, 3),
                            "edge": round(edge, 3),
                            "market": "over25",
                            "probs": pr,
                            "exp_g": exp_g,
                            "home_form": round(hf,2),
                            "away_form": round(af,2),
                            "has_real_stats": has_real
                        })

            # GG / Both Teams to Score
            if "both teams to score" in market_name or "goal" in market_name:
                for ch in choices:
                    name_ch = ch.get("name", "").lower()
                    if "yes" in name_ch or "gg" in name_ch:
                        odds_val = float(ch.get("odds", 0))
                        if 1.40 <= odds_val <= 2.60:
                            prob = pr["gg"]
                            edge = prob - 1 / odds_val if odds_val > 0 else 0
                            picks.append({
                                "name": "Goal/Goal",
                                "odds": round(odds_val, 2),
                                "prob": round(prob, 3),
                                "edge": round(edge, 3),
                                "market": "gg",
                                "probs": pr,
                                "exp_g": exp_g,
                                "home_form": round(hf,2),
                                "away_form": round(af,2),
                                "has_real_stats": has_real
                            })

        # Score come prima
        return [{
            **p,
            "match": f"{home} vs {away}",
            "league": f"{dummy_league['flag']} {dummy_league['name']}",
            "commence_time": commence_time,
            "score": p["edge"]*50 + p["prob"]*30 + (hf+af)*10 + (10 if has_real else 0)
        } for p in picks if p["edge"] is not None]

    except Exception as e:
        print(f"Errore parsing evento Sofascore: {str(e)}")
        return []

# ── Combo ──────────────────────────────────────────────────────────────────────
def find_best_combo(picks, target, cfg):
    for min_edge in [0.03, 0.01, 0.0, -0.05]:
        filtered = [p for p in picks if p["edge"] >= min_edge]
        if len(filtered) >= cfg["min_picks"]: break
    if len(filtered) < cfg["min_picks"]: filtered = picks

    top = sorted(filtered, key=lambda p: p["score"], reverse=True)[:25]
    best, best_score = [], -1

    for sz in range(cfg["min_picks"], cfg["max_picks"]+1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            if len({p["match"] for p in combo}) != sz: continue
            mc = {}
            for p in combo: mc[p["market"]] = mc.get(p["market"], 0) + 1
            if any(v > 2 for v in mc.values()): continue
            tot = math.prod(p["odds"] for p in combo)
            if tot < target * 0.55 or tot > target * 1.55: continue
            combo_prob = math.prod(p["prob"] for p in combo)
            diff_pen = abs(tot - target) / target
            score = combo_prob * 70 + sum(p["edge"] for p in combo) * 15 - diff_pen * 15
            if score > best_score:
                best_score = score
                best = list(combo)
        if best and abs(math.prod(p["odds"] for p in best) - target) / target < 0.15:
            break
    return best

# ── Routes ─────────────────────────────────────────────────────────────────────
@app.route("/health")
def health():
    with db_lock:
        conn = get_db()
        stats_count = conn.execute("SELECT COUNT(*) FROM team_stats").fetchone()[0]
        odds_count  = conn.execute("SELECT COUNT(*) FROM odds_cache").fetchone()[0]
        last_job    = conn.execute("SELECT * FROM job_log ORDER BY id DESC LIMIT 1").fetchone()
        conn.close()
    return jsonify({
        "status": "ok",
        "db_team_stats": stats_count,
        "db_odds_cache": odds_count,
        "last_job": dict(last_job) if last_job else None,
    })

@app.route("/sync", methods=["POST"])
def sync_stats():
    body   = request.get_json() or {}
    fd_key = (body.get("football_api_key") or "").strip()
    if not fd_key:
        return jsonify({"error": "football_api_key mancante"}), 400

    def run_sync():
        fd_codes = ["PL", "SA", "PD", "BL1", "FL1", "CL", "EL", "PPL", "DED"]
        results = {}
        for code in fd_codes:
            count = sync_league_stats(code, fd_key)  # tieni se vuoi stats da fd
            results[code] = count
        with db_lock:
            conn = get_db()
            conn.execute("INSERT INTO job_log (job_name, status, message, ran_at) VALUES (?,?,?,?)",
                ("sync_stats", "ok", str(results), datetime.now(timezone.utc).isoformat()))
            conn.commit()
            conn.close()

    t = threading.Thread(target=run_sync, daemon=True)
    t.start()
    return jsonify({"status": "sync avviato in background"})

@app.route("/generate", methods=["POST"])
def generate():
    body   = request.get_json() or {}
    target = float(body.get("target", 3.0))

    now_utc = datetime.now(timezone.utc)
    italy_offset = 1 if now_utc.month in [1,2,11,12] else 2  # semplificato DST
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    all_picks = []
    cache_used = False
    day_label = "oggi"

    for day_offset in range(3):
        day_dt = now_italy.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start = now_utc if day_offset == 0 else day_dt.astimezone(timezone.utc)
        end = (day_dt + timedelta(days=1)).astimezone(timezone.utc) - timedelta(seconds=1)

        events, from_cache = fetch_sofascore_day(date_str, start, end)
        if from_cache:
            cache_used = True

        day_picks = []
        for ev in events:
            picks_ev = analyze_event_sofa(ev)
            day_picks.extend(picks_ev)

        if day_picks:
            all_picks = day_picks
            day_label = "oggi" if day_offset == 0 else "domani" if day_offset == 1 else "dopodomani"
            break

    if not all_picks:
        return jsonify({"error": "Nessuna partita o quote trovate nei prossimi 3 giorni"}), 404

    # Deduplica
    seen = set()
    unique = []
    for p in all_picks:
        key = f"{p['match']}|{p['name']}"
        if key not in seen:
            seen.add(key)
            unique.append(p)

    TARGETS = [3, 5, 8, 10, 100]
    multiples = []
    used_matches = set()

    for tgt in TARGETS:
        cfg = get_cfg(tgt)
        available = [p for p in unique if p["match"] not in used_matches] or unique
        combo = find_best_combo(available, tgt, cfg)
        if combo:
            for p in combo:
                used_matches.add(p["match"])
            total_odds = round(math.prod(p["odds"] for p in combo), 2)
            combo_prob = round(math.prod(p["prob"] for p in combo) * 100, 1)
            multiples.append({
                "target": tgt,
                "total_odds": total_odds,
                "combo_probability": combo_prob,
                "picks": combo,
                "value_in_combo": sum(1 for p in combo if p["edge"] > 0.02),
            })

    if not multiples:
        return jsonify({"error": "Impossibile generare multiple valide"}), 404

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": sum(1 for p in unique if p["edge"] > 0.02),
        "cache_used": cache_used,
        "source": "Sofascore (non ufficiale)",
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))