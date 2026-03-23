from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, time, json
from datetime import datetime, timezone, timedelta

app = Flask(__name__)
CORS(app)

DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "scommettiamo.db")
db_lock = threading.Lock()

SOFA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Accept": "application/json",
    "Referer": "https://www.sofascore.com/",
}

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
        if target <= k: return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

# ── Database ───────────────────────────────────────────────────────────────────
def get_db():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with db_lock:
        conn = get_db()
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS sofa_team_stats (
                team_id INTEGER,
                tournament_id INTEGER,
                season_id INTEGER,
                goals_scored INTEGER,
                goals_conceded INTEGER,
                big_chances INTEGER,
                shots_on_target INTEGER,
                shots INTEGER,
                matches INTEGER,
                updated_at TEXT,
                PRIMARY KEY (team_id, tournament_id, season_id)
            );
            CREATE TABLE IF NOT EXISTS sofa_events_cache (
                date TEXT PRIMARY KEY,
                data TEXT,
                updated_at TEXT
            );
        """)
        conn.commit()
        conn.close()

init_db()

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

# ── Conversione quota frazionaria → decimale ───────────────────────────────────
def frac_to_dec(frac_str):
    try:
        if "/" in str(frac_str):
            n, d = frac_str.split("/")
            return round(int(n) / int(d) + 1, 3)
        return float(frac_str) + 1
    except:
        return None

# ── SofaScore API ─────────────────────────────────────────────────────────────
def sofa_get(url, timeout=8):
    try:
        r = requests.get(url, headers=SOFA_HEADERS, timeout=timeout)
        if r.ok: return r.json()
    except: pass
    return None

def get_team_stats(team_id, tournament_id, season_id):
    """Recupera statistiche squadra — prima dal DB, poi da SofaScore"""
    with db_lock:
        conn = get_db()
        row = conn.execute(
            "SELECT * FROM sofa_team_stats WHERE team_id=? AND tournament_id=? AND season_id=?",
            (team_id, tournament_id, season_id)
        ).fetchone()
        conn.close()

    if row:
        updated = datetime.fromisoformat(row["updated_at"])
        age = (datetime.now(timezone.utc) - updated).total_seconds()
        if age < 3600 * 12:  # fresco per 12 ore
            return dict(row)

    # Fetch da SofaScore
    data = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{tournament_id}/season/{season_id}/statistics/overall")
    if not data: return None
    stats = data.get("statistics", {})
    if not stats: return None

    matches = stats.get("matches") or 1
    result = {
        "team_id": team_id,
        "tournament_id": tournament_id,
        "season_id": season_id,
        "goals_scored": stats.get("goalsScored") or 0,
        "goals_conceded": stats.get("goalsConceded") or 0,
        "big_chances": stats.get("bigChances") or 0,
        "shots_on_target": stats.get("shotsOnTarget") or 0,
        "shots": stats.get("shots") or 0,
        "matches": matches,
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }

    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO sofa_team_stats
            (team_id, tournament_id, season_id, goals_scored, goals_conceded,
             big_chances, shots_on_target, shots, matches, updated_at)
            VALUES (?,?,?,?,?,?,?,?,?,?)
        """, tuple(result.values()))
        conn.commit()
        conn.close()

    return result

def calc_xg_proxy(stats):
    """Calcola xG proxy da bigChances e shots on target"""
    if not stats: return LEAGUE_AVG
    m = stats["matches"] or 1
    bc  = stats["big_chances"] / m
    sot = stats["shots_on_target"] / m
    sh  = stats["shots"] / m
    return round(bc * 0.35 + sot * 0.10 + sh * 0.03, 3)

def calc_lambda(h_stats, a_stats):
    """Lambda incrociati usando xG proxy e media gol"""
    avg = LEAGUE_AVG

    if h_stats and a_stats:
        hm = h_stats["matches"] or 1
        am = a_stats["matches"] or 1

        # Media gol normalizzata
        att_h = (h_stats["goals_scored"] / hm) / avg
        att_a = (a_stats["goals_scored"] / am) / avg
        def_h = (h_stats["goals_conceded"] / hm) / avg
        def_a = (a_stats["goals_conceded"] / am) / avg

        # xG proxy
        xg_h = calc_xg_proxy(h_stats)
        xg_a = calc_xg_proxy(a_stats)

        # Lambda incrociato: media gol × difesa avversaria, corretto con xG
        lh_goals = avg * att_h * def_a
        la_goals = avg * att_a * def_h

        # Fusione 60% gol reali + 40% xG proxy
        lh = lh_goals * 0.60 + xg_h * 0.40
        la = la_goals * 0.60 + xg_a * 0.40

    elif h_stats:
        lh = calc_xg_proxy(h_stats)
        la = avg
    elif a_stats:
        lh = avg
        la = calc_xg_proxy(a_stats)
    else:
        lh = la = avg

    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

def get_event_odds(event_id):
    """Recupera quote Over/Under da SofaScore"""
    data = sofa_get(f"https://api.sofascore.com/api/v1/event/{event_id}/odds/1/all")
    if not data: return {}

    odds = {}
    for market in data.get("markets", []):
        mg = market.get("marketGroup", "")
        choices = market.get("choices", [])

        if "Over/Under" in mg or "Goals" in mg:
            for ch in choices:
                name = ch.get("name", "")
                frac = ch.get("fractionalValue") or ch.get("initialFractionalValue")
                dec = frac_to_dec(frac)
                if dec and dec > 1:
                    odds[name] = dec

    return odds

def get_today_events(date_str):
    """Recupera tutti gli eventi football di oggi da SofaScore con cache DB"""
    with db_lock:
        conn = get_db()
        row = conn.execute("SELECT data, updated_at FROM sofa_events_cache WHERE date=?", (date_str,)).fetchone()
        conn.close()

    if row:
        updated = datetime.fromisoformat(row["updated_at"])
        age = (datetime.now(timezone.utc) - updated).total_seconds()
        if age < 3600 * 2:  # cache 2 ore
            return json.loads(row["data"])

    data = sofa_get(f"https://api.sofascore.com/api/v1/sport/football/scheduled-events/{date_str}", timeout=12)
    if not data: return []
    events = data.get("events", [])

    with db_lock:
        conn = get_db()
        conn.execute(
            "INSERT OR REPLACE INTO sofa_events_cache (date, data, updated_at) VALUES (?,?,?)",
            (date_str, json.dumps(events), datetime.now(timezone.utc).isoformat())
        )
        conn.commit()
        conn.close()

    return events

def analyze_event(event, now_utc, end_utc):
    """Analizza un singolo evento SofaScore"""
    ct = event.get("startTimestamp")
    if not ct: return []
    event_time = datetime.fromtimestamp(ct, tz=timezone.utc)
    if not (now_utc <= event_time <= end_utc): return []

    # Salta eventi già iniziati o non programmati
    status = event.get("status", {}).get("type", "")
    if status in ["inprogress", "finished", "postponed", "canceled"]: return []

    home_team = event.get("homeTeam", {})
    away_team = event.get("awayTeam", {})
    home_name = home_team.get("name", "")
    away_name = away_team.get("name", "")
    home_id   = home_team.get("id")
    away_id   = away_team.get("id")
    event_id  = event.get("id")
    tournament = event.get("tournament", {})
    league_name = tournament.get("name", "")
    category = tournament.get("category", {})
    country_flag = category.get("flag", "").title()
    unique_t = tournament.get("uniqueTournament", {})
    t_id = unique_t.get("id")
    s_id = event.get("season", {}).get("id")

    # Statistiche squadre
    h_stats = get_team_stats(home_id, t_id, s_id) if home_id and t_id and s_id else None
    a_stats = get_team_stats(away_id, t_id, s_id) if away_id and t_id and s_id else None
    has_real = bool(h_stats or a_stats)

    lh, la = calc_lambda(h_stats, a_stats)
    pr = calc_probs(lh, la)
    exp_g = round(lh + la, 2)

    # Quote da SofaScore
    odds_data = get_event_odds(event_id)

    picks = []

    # Over 1.5
    o15_odds = odds_data.get("Over 1.5") or odds_data.get("Over1.5")
    if o15_odds and 1.10 <= o15_odds <= 1.65:
        prob = pr["over15"]
        edge = prob - 1/o15_odds
        picks.append({"name": "Over 1.5", "odds": round(o15_odds,2), "prob": round(prob,3),
            "edge": round(edge,3), "market": "over15"})

    # Over 2.5
    o25_odds = odds_data.get("Over 2.5") or odds_data.get("Over2.5")
    if o25_odds and 1.35 <= o25_odds <= 2.60:
        prob = pr["over25"]
        edge = prob - 1/o25_odds
        picks.append({"name": "Over 2.5", "odds": round(o25_odds,2), "prob": round(prob,3),
            "edge": round(edge,3), "market": "over25"})

    # GG — stima dalla probabilità Poisson se non disponibile nelle quote
    gg_odds = odds_data.get("Yes") or odds_data.get("GG")
    if not gg_odds:
        prob_gg = pr["gg"]
        if prob_gg > 0.45:
            gg_odds = round(1 / prob_gg * 1.05, 2)
    if gg_odds and 1.40 <= gg_odds <= 2.50:
        prob = pr["gg"]
        edge = prob - 1/gg_odds
        picks.append({"name": "Goal/Goal", "odds": round(gg_odds,2), "prob": round(prob,3),
            "edge": round(edge,3), "market": "gg"})

    if not picks: return []

    flag_map = {"england": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "italy": "🇮🇹", "spain": "🇪🇸", "germany": "🇩🇪",
                "france": "🇫🇷", "portugal": "🇵🇹", "netherlands": "🇳🇱",
                "brazil": "🇧🇷", "argentina": "🇦🇷", "usa": "🇺🇸",
                "turkey": "🇹🇷", "greece": "🇬🇷", "belgium": "🇧🇪"}
    cf = category.get("flag", "").lower()
    flag = flag_map.get(cf, "⚽")

    return [{**p,
        "match": f"{home_name} vs {away_name}",
        "league": f"{flag} {league_name}",
        "commence_time": datetime.fromtimestamp(ct, tz=timezone.utc).isoformat(),
        "probs": pr, "exp_g": exp_g,
        "home_form": 0.5, "away_form": 0.5,
        "has_real_stats": has_real,
        "score": p["edge"]*50 + p["prob"]*30 + (15 if has_real else 0),
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

# ── Routes ─────────────────────────────────────────────────────────────────────
@app.route("/health")
def health():
    with db_lock:
        conn = get_db()
        stats_count = conn.execute("SELECT COUNT(*) as c FROM sofa_team_stats").fetchone()["c"]
        events_count = conn.execute("SELECT COUNT(*) as c FROM sofa_events_cache").fetchone()["c"]
        conn.close()
    return jsonify({"status": "ok", "team_stats_cached": stats_count, "events_cached": events_count})

@app.route("/generate", methods=["POST"])
def generate():
    body   = request.get_json() or {}
    target = float(body.get("target", 3))

    now_utc = datetime.now(timezone.utc)
    italy_offset = 2 if now_utc.month in [4,5,6,7,8,9,10] else 1
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    all_picks = []
    day_offset = 0

    for day_offset in range(3):
        day_dt   = now_italy.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start    = now_utc if day_offset == 0 else day_dt.astimezone(timezone.utc)
        end      = (now_italy.replace(hour=23, minute=59, second=59) + timedelta(days=day_offset)).astimezone(timezone.utc)

        events = get_today_events(date_str)
        day_picks = []
        for ev in events:
            day_picks.extend(analyze_event(ev, start, end))

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

    TARGETS = [3, 5, 8, 10, 100]
    multiples = []
    used_matches = set()

    for tgt in TARGETS:
        cfg = get_cfg(tgt)
        available = [p for p in unique if p["match"] not in used_matches] or unique
        combo = find_best_combo(available, tgt, cfg)
        if combo:
            for p in combo: used_matches.add(p["match"])
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
        return jsonify({"error": "Impossibile costruire multipla. Riprova più tardi."}), 404

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "leagues_with_data": len({p["league"] for p in unique}),
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": sum(1 for p in unique if p["edge"] > 0.02),
        "source": "sofascore",
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
