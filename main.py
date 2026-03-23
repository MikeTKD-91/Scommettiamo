from flask import Flask, request, jsonify
from flask_cors import CORS
import requests
import math
import itertools
import os
import sqlite3
import threading
import time
import random
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

TARGET_CONFIG = {
    3:   {"min_picks": 2, "max_picks": 3},
    5:   {"min_picks": 3, "max_picks": 4},
    8:   {"min_picks": 4, "max_picks": 5},
    10:  {"min_picks": 4, "max_picks": 6},
    100: {"min_picks": 6, "max_picks": 9},
}

def get_cfg(target):
    for k in sorted(TARGET_CONFIG.keys()):
        if target <= k:
            return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

# ── Poisson + Dixon-Coles ──────────────────────────────────────────────────────
def dc_tau(x, y, lh, la, rho=-0.13):
    if x == 0 and y == 0: return max(0.001, 1 - lh * la * rho)
    if x == 0 and y == 1: return max(0.001, 1 + lh * rho)
    if x == 1 and y == 0: return max(0.001, 1 + la * rho)
    if x == 1 and y == 1: return max(0.001, 1 - rho)
    return 1.0

def pmf(lam, k):
    if lam <= 0: return 0.0
    try:
        return math.exp(k * math.log(lam) - lam - sum(math.log(i) for i in range(1, k+1)))
    except:
        return 0.0

def calc_probs(lh, la):
    o15 = o25 = gg = 0.0
    for h in range(0, 10):
        for a in range(0, 10):
            p = pmf(lh, h) * pmf(la, a) * dc_tau(h, a, lh, la)
            t = h + a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if h > 0 and a > 0: gg += p
    return {
        "over15": min(o15, 0.99),
        "over25": min(o25, 0.99),
        "gg": min(gg, 0.99)
    }

# ── Stats dal DB ───────────────────────────────────────────────────────────────
def get_stats_from_db(team_name, fd_code=None, season="2025"):
    with db_lock:
        conn = get_db()
        if fd_code:
            row = conn.execute(
                "SELECT * FROM team_stats WHERE team_name=? AND fd_code=? AND season=?",
                (team_name, fd_code, season)
            ).fetchone()
        else:
            row = conn.execute(
                "SELECT * FROM team_stats WHERE team_name=? AND season=?",
                (team_name, season)
            ).fetchone()
        conn.close()
    return dict(row) if row else None

def save_stats_to_db(team_name, fd_code, season, stats):
    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO team_stats
            (team_name, fd_code, season, att_h, att_a, def_h, def_a, wf_home, wf_away, home_advantage, form, updated_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            team_name, fd_code or "", season,
            stats.get("att_h", 1.0), stats.get("att_a", 1.0),
            stats.get("def_h", 1.0), stats.get("def_a", 1.0),
            stats.get("wf_home", 0.5), stats.get("wf_away", 0.5),
            stats.get("home_advantage", 1.15),
            stats.get("form", ""),
            datetime.now(timezone.utc).isoformat()
        ))
        conn.commit()
        conn.close()

# ── Lambda e form ──────────────────────────────────────────────────────────────
def calc_lambda(hs, as_):
    avg = LEAGUE_AVG
    if hs and as_:
        lh = avg * hs["att_h"] * as_["def_a"] * min(hs.get("home_advantage", 1.2), 1.4)
        la = avg * as_["att_a"] * hs["def_h"]
        lh *= 0.85 + hs.get("wf_home", 0.5) * 0.30
        la *= 0.85 + as_.get("wf_away", 0.5) * 0.30
    else:
        lh = la = avg
    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

def form_score(form):
    if not form: return 0.5
    last5 = form[-5:]
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in last5) / 15

# ── Sofascore ──────────────────────────────────────────────────────────────────
SOFA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Referer": "https://www.sofascore.com/",
    "Accept": "*/*",
    "Accept-Language": "it-IT,it;q=0.9",
}

SOFA_CACHE_TTL = 3600 * 1.5

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
        conn.execute(
            "INSERT OR REPLACE INTO odds_cache (date, league_key, data, updated_at) VALUES (?,?,?,?)",
            (date_str, "sofascore", json.dumps(data), datetime.now(timezone.utc).isoformat())
        )
        conn.commit()
        conn.close()

def try_odds_endpoints(event_id):
    variants = [
        f"/odds/1/all",
        f"/odds/1/full",
        f"/odds/average",
        f"/markets",
    ]
    for path in variants:
        url = f"https://api.sofascore.com/api/v1/event/{event_id}{path}"
        try:
            r = requests.get(url, headers=SOFA_HEADERS, timeout=8)
            if r.ok and r.json():
                print(f"→ Trovato odds su: {path}")
                return r.json()
        except:
            pass
    print("× Nessun endpoint odds valido trovato")
    return {}

def fetch_sofascore_day(date_str, start_utc, end_utc):
    cached = get_sofascore_cache(date_str)
    if cached:
        print(f"[CACHE HIT] {date_str}")
        return cached, True

    url = f"https://api.sofascore.com/api/v1/sport/football/scheduled-events/{date_str}"
    print(f"Fetch scheduled-events: {date_str}")
    try:
        r = requests.get(url, headers=SOFA_HEADERS, timeout=12)
        if not r.ok:
            print(f"Errore scheduled-events: {r.status_code}")
            return [], False

        events = r.json().get("events", [])
        print(f"Trovati {len(events)} eventi programmati")

        processed = []
        for ev in events[:30]:  # limita per test
            if ev.get("status", {}).get("type") != "scheduled":
                continue
            ts = ev.get("startTimestamp")
            if not ts:
                continue
            ev_time = datetime.fromtimestamp(ts, tz=timezone.utc)
            if not (start_utc <= ev_time <= end_utc):
                continue

            time.sleep(3 + random.uniform(0, 3))
            detail_url = f"https://api.sofascore.com/api/v1/event/{ev['id']}"
            rd = requests.get(detail_url, headers=SOFA_HEADERS, timeout=8)
            detail = rd.json().get("event", {}) if rd.ok else {}

            time.sleep(3 + random.uniform(0, 3))
            odds = try_odds_endpoints(ev["id"])

            ev_copy = ev.copy()
            ev_copy["detail"] = detail
            ev_copy["odds"] = odds
            processed.append(ev_copy)
            print(f"  Elaborata: {detail.get('homeTeam',{}).get('name','?')} - {detail.get('awayTeam',{}).get('name','?')}")

        if processed:
            save_sofascore_cache(date_str, processed)
        return processed, False

    except Exception as e:
        print(f"Eccezione fetch Sofascore: {str(e)}")
        return [], False

# ── Analisi evento Sofascore ───────────────────────────────────────────────────
def analyze_event_sofa(ev):
    try:
        detail = ev.get("detail", {})
        home = detail.get("homeTeam", {}).get("name", "Home")
        away = detail.get("awayTeam", {}).get("name", "Away")
        commence = datetime.fromtimestamp(ev.get("startTimestamp", 0), tz=timezone.utc).isoformat()

        print(f"→ Analisi: {home} vs {away}")

        hs = get_stats_from_db(home)
        as_ = get_stats_from_db(away)
        lh, la = calc_lambda(hs, as_)
        pr = calc_probs(lh, la)
        hf = form_score(hs.get("form", "") if hs else "")
        af = form_score(as_.get("form", "") if as_ else "")

        picks = []

        odds_raw = ev.get("odds", {})
        markets = []

        if isinstance(odds_raw, dict):
            if "markets" in odds_raw:
                markets = odds_raw["markets"]
            elif "market" in odds_raw:
                markets = [odds_raw["market"]]

        print(f"  Markets trovati: {len(markets)}")

        for market in markets:
            m_name = str(market.get("marketName", "") or market.get("name", "") or market.get("marketId", "")).lower()
            choices = market.get("choices", []) or market.get("outcomes", [])

            for ch in choices:
                ch_name = str(ch.get("name", "")).lower()
                odds_val = float(ch.get("odds", 0) or ch.get("odd", 0) or 0)
                point = ch.get("point", None) or ch.get("line", None)

                if odds_val < 1.01:
                    continue

                if "over" in ch_name or ("over" in m_name and point):
                    if point == 1.5 or (point is None and "1.5" in ch_name):
                        prob = pr["over15"]
                        edge = prob - 1/odds_val
                        picks.append({
                            "name": "Over 1.5",
                            "odds": round(odds_val, 2),
                            "prob": round(prob, 3),
                            "edge": round(edge, 3),
                            "market": "over15",
                            "probs": pr,
                            "exp_g": round(lh + la, 2),
                            "home_form": round(hf,2),
                            "away_form": round(af,2),
                            "has_real_stats": bool(hs or as_),
                            "score": edge*50 + prob*30 + (hf+af)*10 + (10 if hs or as_ else 0)
                        })
                    if point == 2.5 or (point is None and "2.5" in ch_name):
                        prob = pr["over25"]
                        edge = prob - 1/odds_val
                        picks.append({
                            "name": "Over 2.5",
                            "odds": round(odds_val, 2),
                            "prob": round(prob, 3),
                            "edge": round(edge, 3),
                            "market": "over25",
                            "probs": pr,
                            "exp_g": round(lh + la, 2),
                            "home_form": round(hf,2),
                            "away_form": round(af,2),
                            "has_real_stats": bool(hs or as_),
                            "score": edge*50 + prob*30 + (hf+af)*10 + (10 if hs or as_ else 0)
                        })

                if "both" in m_name or "goal" in m_name or "gg" in m_name or "score" in m_name:
                    if "yes" in ch_name or "gg" in ch_name:
                        prob = pr["gg"]
                        edge = prob - 1/odds_val
                        picks.append({
                            "name": "Goal/Goal",
                            "odds": round(odds_val, 2),
                            "prob": round(prob, 3),
                            "edge": round(edge, 3),
                            "market": "gg",
                            "probs": pr,
                            "exp_g": round(lh + la, 2),
                            "home_form": round(hf,2),
                            "away_form": round(af,2),
                            "has_real_stats": bool(hs or as_),
                            "score": edge*50 + prob*30 + (hf+af)*10 + (10 if hs or as_ else 0)
                        })

        print(f"  Picks generati: {len(picks)}")
        return picks

    except Exception as e:
        print(f"Errore grave in analyze_event_sofa: {str(e)}")
        return []

# ── Combo ──────────────────────────────────────────────────────────────────────
def find_best_combo(picks, target, cfg):
    if not picks:
        return None

    for min_edge in [0.04, 0.02, 0.0, -0.04]:
        filtered = [p for p in picks if p["edge"] >= min_edge]
        if len(filtered) >= cfg["min_picks"]:
            break
    else:
        filtered = picks

    if len(filtered) < cfg["min_picks"]:
        return None

    top = sorted(filtered, key=lambda p: p["score"], reverse=True)[:30]

    best = None
    best_score = -1

    for size in range(cfg["min_picks"], cfg["max_picks"] + 1):
        if len(top) < size:
            continue
        for combo in itertools.combinations(top, size):
            if len(set(p["match"] for p in combo)) != size:
                continue
            markets_count = {}
            for p in combo:
                markets_count[p["market"]] = markets_count.get(p["market"], 0) + 1
            if any(v > 2 for v in markets_count.values()):
                continue
            total_odds = math.prod(p["odds"] for p in combo)
            if total_odds < target * 0.6 or total_odds > target * 1.6:
                continue
            combo_prob = math.prod(p["prob"] for p in combo)
            diff_penalty = abs(total_odds - target) / target
            score = combo_prob * 75 + sum(p["edge"] for p in combo) * 15 - diff_penalty * 20
            if score > best_score:
                best_score = score
                best = list(combo)

    return best

# ── Route principale ───────────────────────────────────────────────────────────
@app.route("/generate", methods=["POST"])
def generate():
    body = request.get_json() or {}
    target = float(body.get("target", 3.0))

    now_utc = datetime.now(timezone.utc)
    italy_offset = 1 if now_utc.month in [1,2,11,12] else 2  # approssimativo
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    print("\n=== INIZIO GENERA ===")
    all_picks = []
    cache_used = False
    day_label = "oggi"

    for offset in range(3):
        day_dt = now_italy.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start = now_utc if offset == 0 else day_dt.astimezone(timezone.utc)
        end = (day_dt + timedelta(days=1)).astimezone(timezone.utc) - timedelta(seconds=1)

        print(f"\nGiorno {offset}: {date_str}")
        events, from_cache = fetch_sofascore_day(date_str, start, end)
        if from_cache:
            cache_used = True

        day_picks = []
        for ev in events:
            match_name = f"{ev.get('detail',{}).get('homeTeam',{}).get('name','?')} vs {ev.get('detail',{}).get('awayTeam',{}).get('name','?')}"
            print(f"  → {match_name}")
            picks = analyze_event_sofa(ev)
            for p in picks:
                p["match"] = match_name
                p["league"] = "Sofascore"
                p["commence_time"] = ev.get("startTimestamp")
            day_picks.extend(picks)

        print(f"  Tot picks giorno: {len(day_picks)}")
        if day_picks:
            all_picks = day_picks
            day_label = ["oggi", "domani", "dopodomani"][offset]
            break

    if not all_picks:
        print("NESSUN PICK TROVATO")
        return jsonify({"error": "Nessuna partita con quote valida trovata nei prossimi 3 giorni"}), 404

    # Deduplica
    seen = set()
    unique = []
    for p in all_picks:
        key = f"{p.get('match','')} | {p.get('name','')}"
        if key not in seen:
            seen.add(key)
            unique.append(p)

    print(f"Pick unici totali: {len(unique)}")

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
                "value_in_combo": sum(1 for p in combo if p["edge"] > 0.015),
            })

    if not multiples:
        print("NESSUNA COMBINAZIONE VALIDA TROVATA")
        return jsonify({
            "error": "Impossibile costruire multipla – probabilmente nessuna value bet valida o quote insufficienti",
            "debug": {
                "picks_totali": len(all_picks),
                "picks_unici": len(unique),
                "giorno": day_label
            }
        }), 200  # 200 per vedere debug

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "matches_analyzed": len(set(p["match"] for p in unique)),
        "value_bets_found": sum(1 for p in unique if p["edge"] > 0.015),
        "cache_used": cache_used,
        "source": "Sofascore (API interna non ufficiale)"
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=True)