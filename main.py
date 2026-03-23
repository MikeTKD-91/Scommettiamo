from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, time
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

LEAGUES = [
    {"key": "soccer_epl",                        "name": "Premier League",    "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": "PL"},
    {"key": "soccer_italy_serie_a",              "name": "Serie A",           "flag": "🇮🇹",  "fd_code": "SA"},
    {"key": "soccer_spain_la_liga",              "name": "La Liga",           "flag": "🇪🇸",  "fd_code": "PD"},
    {"key": "soccer_germany_bundesliga",         "name": "Bundesliga",        "flag": "🇩🇪",  "fd_code": "BL1"},
    {"key": "soccer_france_ligue_one",           "name": "Ligue 1",           "flag": "🇫🇷",  "fd_code": "FL1"},
    {"key": "soccer_efl_champ",                  "name": "Championship",      "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_italy_serie_b",              "name": "Serie B",           "flag": "🇮🇹",  "fd_code": None},
    {"key": "soccer_spain_segunda_division",     "name": "La Liga 2",         "flag": "🇪🇸",  "fd_code": None},
    {"key": "soccer_germany_bundesliga2",        "name": "Bundesliga 2",      "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_uefa_champs_league",         "name": "Champions League",  "flag": "🏆",   "fd_code": "CL"},
    {"key": "soccer_england_league1",            "name": "League One",        "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_germany_liga3",              "name": "3. Liga",           "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_portugal_primeira_liga",     "name": "Primeira Liga",     "flag": "🇵🇹",  "fd_code": "PPL"},
    {"key": "soccer_netherlands_eredivisie",     "name": "Eredivisie",        "flag": "🇳🇱",  "fd_code": "DED"},
    {"key": "soccer_uefa_europa_league",         "name": "Europa League",     "flag": "🏆",   "fd_code": "EL"},
    {"key": "soccer_uefa_europa_conference_league", "name": "Conference League", "flag": "🏆", "fd_code": None},
    {"key": "soccer_france_ligue_two",           "name": "Ligue 2",           "flag": "🇫🇷",  "fd_code": None},
    {"key": "soccer_belgium_first_div",          "name": "Jupiler Pro",       "flag": "🇧🇪",  "fd_code": None},
    {"key": "soccer_greece_super_league",        "name": "Super League",      "flag": "🇬🇷",  "fd_code": None},
    {"key": "soccer_turkey_super_lig",           "name": "Süper Lig",         "flag": "🇹🇷",  "fd_code": None},
    {"key": "soccer_brazil_campeonato",          "name": "Brasil Série A",    "flag": "🇧🇷",  "fd_code": None},
    {"key": "soccer_argentina_primera_division", "name": "Primera División",  "flag": "🇦🇷",  "fd_code": None},
    {"key": "soccer_usa_mls",                    "name": "MLS",               "flag": "🇺🇸",  "fd_code": None},
    {"key": "soccer_japan_j_league",             "name": "J-League",          "flag": "🇯🇵",  "fd_code": None},
    {"key": "soccer_mexico_ligamx",              "name": "Liga MX",           "flag": "🇲🇽",  "fd_code": None},
]

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
def get_stats_from_db(team_name, fd_code, season="2024"):
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

# ── football-data.org sync ─────────────────────────────────────────────────────
def weighted_form(matches_data, is_home):
    n = len(matches_data)
    if n == 0: return 0.5
    total_w = total_pts = 0
    for i, m in enumerate(matches_data):
        w = n - i
        total_w += w
        r = m["result_home"] if is_home else m["result_away"]
        pts = 3 if r == "W" else 1 if r == "D" else 0
        total_pts += pts * w
    return total_pts / (total_w * 3)

def fetch_team_stats_fd(team_name, team_id, fd_code, fd_key, season="2024"):
    """Scarica stats squadra da football-data.org e salva nel DB"""
    existing = get_stats_from_db(team_name, fd_code, season)
    if existing:
        updated = datetime.fromisoformat(existing["updated_at"])
        if (datetime.now(timezone.utc) - updated).total_seconds() < 3600 * 12:
            return existing  # fresco, non aggiornare

    try:
        r = requests.get(
            f"https://api.football-data.org/v4/teams/{team_id}/matches?status=FINISHED&limit=10",
            headers={"X-Auth-Token": fd_key}, timeout=8
        )
        if not r.ok: return existing
        matches = r.json().get("matches", [])
        if not matches: return existing

        home_m, away_m = [], []
        gfh = gfa = gah = gaa = ph = pa = 0
        for m in matches:
            hn = m["homeTeam"]["name"]
            sc = m["score"]["fullTime"]
            gh = sc.get("home", 0) or 0
            ga = sc.get("away", 0) or 0
            is_home = team_name.lower() in hn.lower() or hn.lower() in team_name.lower()
            if is_home:
                gfh += gh; gah += ga; ph += 1
                home_m.append({"result_home": "W" if gh>ga else "D" if gh==ga else "L"})
            else:
                gfa += ga; gaa += gh; pa += 1
                away_m.append({"result_away": "W" if ga>gh else "D" if ga==gh else "L"})

        stats = {
            "att_h": (gfh/ph/LEAGUE_AVG) if ph > 0 else 1.0,
            "att_a": (gfa/pa/LEAGUE_AVG) if pa > 0 else 1.0,
            "def_h": (gah/ph/LEAGUE_AVG) if ph > 0 else 1.0,
            "def_a": (gaa/pa/LEAGUE_AVG) if pa > 0 else 1.0,
            "wf_home": weighted_form(home_m, True),
            "wf_away": weighted_form(away_m, False),
            "home_advantage": min((gfh/ph)/(gfa/pa) if ph>0 and pa>0 and gfa>0 else 1.15, 2.0),
            "form": "".join([m["result_home"] for m in home_m] + [m["result_away"] for m in away_m])[-10:],
        }
        save_stats_to_db(team_name, fd_code, season, stats)
        return get_stats_from_db(team_name, fd_code, season)
    except:
        return existing

def sync_league_stats(fd_code, fd_key, season="2024"):
    """Sync completo di tutte le squadre di un campionato — chiamato dal job notturno"""
    try:
        r = requests.get(
            f"https://api.football-data.org/v4/competitions/{fd_code}/teams",
            headers={"X-Auth-Token": fd_key}, timeout=10
        )
        if not r.ok: return 0
        teams = r.json().get("teams", [])
        count = 0
        for team in teams:
            fetch_team_stats_fd(team["name"], team["id"], fd_code, fd_key, season)
            count += 1
            time.sleep(0.5)  # rispetta rate limit
        return count
    except:
        return 0

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

# ── Analisi evento ─────────────────────────────────────────────────────────────
def analyze_event(event, league, fd_key):
    home, away = event["home_team"], event["away_team"]
    fd_code = league.get("fd_code")

    # Prova prima dal DB (dati pre-caricati)
    hs  = get_stats_from_db(home, fd_code) if fd_code else None
    as_ = get_stats_from_db(away, fd_code) if fd_code else None

    # Se non nel DB e abbiamo la key, scarica al volo
    if not hs and fd_key and fd_code:
        try:
            r = requests.get(
                f"https://api.football-data.org/v4/competitions/{fd_code}/teams",
                headers={"X-Auth-Token": fd_key}, timeout=6
            )
            if r.ok:
                teams = r.json().get("teams", [])
                for t in teams:
                    nl = home.lower()
                    tn = t["name"].lower()
                    if nl in tn or tn in nl:
                        hs = fetch_team_stats_fd(home, t["id"], fd_code, fd_key)
                    nl2 = away.lower()
                    if nl2 in tn or tn in nl2:
                        as_ = fetch_team_stats_fd(away, t["id"], fd_code, fd_key)
        except: pass

    lh, la = calc_lambda(hs, as_)
    pr = calc_probs(lh, la)
    hf = form_score(hs["form"] if hs else "")
    af = form_score(as_["form"] if as_ else "")
    exp_g = round(lh + la, 2)
    has_real = bool(hs or as_)

    picks = []
    for bk in event.get("bookmakers", []):
        markets = {m["key"]: m for m in bk.get("markets", [])}
        if "totals" not in markets: continue
        for o in markets["totals"]["outcomes"]:
            point = float(o.get("point", 0))
            odds  = float(o["price"])
            name_o = o["name"]
            if point == 1.5 and name_o == "Over":
                prob = pr["over15"]
                edge = prob - 1/odds
                if 1.10 <= odds <= 1.65:
                    picks.append({"name": "Over 1.5", "odds": round(odds,2), "prob": round(prob,3),
                        "edge": round(edge,3), "market": "over15", "probs": pr,
                        "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2), "has_real_stats": has_real})
            if point == 2.5 and name_o == "Over":
                prob = pr["over25"]
                edge = prob - 1/odds
                if 1.35 <= odds <= 2.60:
                    picks.append({"name": "Over 2.5", "odds": round(odds,2), "prob": round(prob,3),
                        "edge": round(edge,3), "market": "over25", "probs": pr,
                        "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2), "has_real_stats": has_real})
                # GG proxy
                prob_gg = pr["gg"]
                est_odds = round(1 / max(prob_gg, 0.01) * 1.05, 2)
                if 1.40 <= est_odds <= 2.50 and prob_gg > 0.45:
                    picks.append({"name": "Goal/Goal", "odds": est_odds, "prob": round(prob_gg,3),
                        "edge": round(prob_gg - 1/est_odds, 3), "market": "gg", "probs": pr,
                        "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2), "has_real_stats": has_real})
        break

    return [{**p, "match": f"{home} vs {away}", "league": f"{league['flag']} {league['name']}",
        "commence_time": event.get("commence_time"),
        "score": p["edge"]*50 + p["prob"]*30 + (hf+af)*10 + (10 if has_real else 0)
    } for p in picks]

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

# ── Odds cache nel DB ──────────────────────────────────────────────────────────
ODDS_CACHE_TTL = 3600 * 2  # 2 ore

def get_odds_from_db(date_str, league_key):
    with db_lock:
        conn = get_db()
        row = conn.execute(
            "SELECT data, updated_at FROM odds_cache WHERE date=? AND league_key=?",
            (date_str, league_key)
        ).fetchone()
        conn.close()
    if not row: return None
    updated = datetime.fromisoformat(row["updated_at"])
    age = (datetime.now(timezone.utc) - updated).total_seconds()
    if age > ODDS_CACHE_TTL: return None
    return json.loads(row["data"])

def save_odds_to_db(date_str, league_key, data):
    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO odds_cache (date, league_key, data, updated_at)
            VALUES (?,?,?,?)
        """, (date_str, league_key, json.dumps(data), datetime.now(timezone.utc).isoformat()))
        conn.commit()
        conn.close()

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
    """Avvia sync in background — risponde subito senza timeout"""
    body   = request.get_json() or {}
    fd_key = (body.get("football_api_key") or "").strip()
    if not fd_key:
        return jsonify({"error": "football_api_key mancante"}), 400

    def run_sync():
        fd_codes = ["PL", "SA", "PD", "BL1", "FL1", "CL", "EL", "PPL", "DED"]
        results = {}
        for code in fd_codes:
            count = sync_league_stats(code, fd_key)
            results[code] = count
        with db_lock:
            conn = get_db()
            conn.execute("INSERT INTO job_log (job_name, status, message, ran_at) VALUES (?,?,?,?)",
                ("sync_stats", "ok", str(results), datetime.now(timezone.utc).isoformat()))
            conn.commit()
            conn.close()

    # Lancia in background senza bloccare la risposta
    t = threading.Thread(target=run_sync, daemon=True)
    t.start()

    return jsonify({"status": "sync avviato in background — controlla /health tra qualche minuto"})

@app.route("/generate", methods=["POST"])
def generate():
    body     = request.get_json() or {}
    odds_key = (body.get("odds_api_key") or "").strip()
    fd_key   = (body.get("football_api_key") or "").strip() or None
    target   = float(body.get("target", 3))

    if not odds_key:
        return jsonify({"error": "Odds API key mancante"}), 400

    now_utc = datetime.now(timezone.utc)
    italy_offset = 2 if now_utc.month in [4,5,6,7,8,9,10] else 1
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    def fetch_league_odds(league_key, date_str, start_utc, end_utc):
        # Prima controlla DB cache
        cached = get_odds_from_db(date_str, league_key)
        if cached is not None:
            return cached, True

        # Cache miss — chiama API
        try:
            url = f"https://api.the-odds-api.com/v4/sports/{league_key}/odds/?apiKey={odds_key}&regions=eu&markets=totals&oddsFormat=decimal"
            r = requests.get(url, timeout=8)
            if not r.ok:
                try:
                    err = r.json()
                    if isinstance(err, dict) and err.get("error_code") == "OUT_OF_USAGE_CREDITS":
                        return None, "credits"
                except: pass
                return [], False
            events = r.json()
            if isinstance(events, dict) and events.get("error_code") == "OUT_OF_USAGE_CREDITS":
                return None, "credits"
            if not isinstance(events, list): return [], False

            # Filtra per data
            day_events = []
            for ev in events:
                ct = ev.get("commence_time", "")
                if not ct: continue
                try:
                    t = datetime.fromisoformat(ct.replace("Z", "+00:00"))
                    if start_utc <= t <= end_utc:
                        day_events.append(ev)
                except: continue

            if day_events:
                save_odds_to_db(date_str, league_key, day_events)
            return day_events, False
        except:
            return [], False

    # Cerca oggi → domani → dopodomani
    all_picks, leagues_found, day_offset, cache_used = [], [], 0, False

    for day_offset in range(3):
        day_dt   = now_italy.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start    = day_dt.astimezone(timezone.utc)
        end      = (now_italy.replace(hour=23, minute=59, second=59) + timedelta(days=day_offset)).astimezone(timezone.utc)
        if day_offset == 0: start = now_utc

        day_picks = []
        for lg in LEAGUES:
            events, source = fetch_league_odds(lg["key"], date_str, start, end)
            if source == "credits":
                return jsonify({"error": "OUT_OF_USAGE_CREDITS: Crediti Odds API esauriti!"}), 429
            if not events: continue
            if source is True: cache_used = True
            leagues_found.append(lg["name"])
            for ev in events:
                day_picks.extend(analyze_event(ev, lg, fd_key))

        if day_picks:
            all_picks = day_picks
            break

    if not all_picks:
        return jsonify({"error": "Nessuna partita trovata nei prossimi 3 giorni."}), 404

    # Deduplica
    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    day_label = "dopodomani" if day_offset == 2 else "domani" if day_offset == 1 else "oggi"

    # Genera multipla per ogni target — pick non ripetuti
    TARGETS = [3, 5, 8, 10, 100]
    multiples = []
    used_matches = set()

    for tgt in TARGETS:
        cfg = get_cfg(tgt)
        available = [p for p in unique if p["match"] not in used_matches] or unique
        combo = find_best_combo(available, tgt, cfg)
        if combo:
            for p in combo: used_matches.add(p["match"])
            total_odds  = round(math.prod(p["odds"] for p in combo), 2)
            combo_prob  = round(math.prod(p["prob"] for p in combo) * 100, 1)
            multiples.append({
                "target": tgt,
                "total_odds": total_odds,
                "combo_probability": combo_prob,
                "picks": combo,
                "value_in_combo": sum(1 for p in combo if p["edge"] > 0.02),
            })

    if not multiples:
        return jsonify({"error": "Impossibile costruire multipla. Riprova più tardi."}), 404

    # Controlla crediti rimanenti
    credits_info = {}
    try:
        cr = requests.get(
            f"https://api.the-odds-api.com/v4/sports/?apiKey={odds_key}&all=false",
            timeout=5
        )
        credits_info = {
            "remaining": cr.headers.get("x-requests-remaining", "?"),
            "used": cr.headers.get("x-requests-used", "?"),
            "quota": 500,
        }
        try:
            rem = int(credits_info["remaining"])
            credits_info["percent_remaining"] = round(rem / 500 * 100)
        except:
            credits_info["percent_remaining"] = None
    except: pass

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "leagues_with_data": len(set(leagues_found)),
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": sum(1 for p in unique if p["edge"] > 0.02),
        "football_api_used": fd_key is not None,
        "cache_used": cache_used,
        "credits": credits_info,
    })

@app.route("/credits", methods=["POST"])
def check_credits():
    body = request.get_json() or {}
    odds_key = (body.get("odds_api_key") or "").strip()
    if not odds_key:
        return jsonify({"error": "Odds API key mancante"}), 400
    try:
        r = requests.get(
            f"https://api.the-odds-api.com/v4/sports/?apiKey={odds_key}&all=false",
            timeout=8
        )
        remaining = r.headers.get("x-requests-remaining", "?")
        used      = r.headers.get("x-requests-used", "?")
        quota     = 500  # piano gratuito
        try:
            pct = round(int(remaining) / quota * 100)
        except:
            pct = None
        return jsonify({
            "remaining": remaining,
            "used": used,
            "quota": quota,
            "percent_remaining": pct,
            "status": "ok" if r.ok else "error",
        })
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
