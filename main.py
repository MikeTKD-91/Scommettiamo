from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, json, logging, time
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import wraps

# â”€â”€ Logging â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler("scommettiamo.log", encoding="utf-8"),
    ]
)
log = logging.getLogger("scommettiamo")

app = Flask(__name__)
CORS(app)

DB_PATH  = os.path.join(os.path.dirname(os.path.abspath(__file__)), "scommettiamo.db")
db_lock  = threading.Lock()
ITALY_TZ = ZoneInfo("Europe/Rome")

SOFA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Accept": "application/json",
    "Referer": "https://www.sofascore.com/",
}

LEAGUE_AVG   = 1.35
MIN_MATCHES  = 5
REGRESSION_K = 10

TARGET_CONFIG = {
    3:   {"min_picks": 2, "max_picks": 3},
    5:   {"min_picks": 3, "max_picks": 4},
    8:   {"min_picks": 4, "max_picks": 5},
    10:  {"min_picks": 4, "max_picks": 6},
    100: {"min_picks": 6, "max_picks": 9},
}

def get_cfg(t):
    for k in sorted(TARGET_CONFIG):
        if t <= k: return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

# â”€â”€ Timing decorator â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def timed(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        t0 = time.perf_counter()
        result = fn(*a, **kw)
        log.info(f"{fn.__name__} completato in {time.perf_counter()-t0:.2f}s")
        return result
    return wrapper

# â”€â”€ Database â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def get_db():
    c = sqlite3.connect(DB_PATH, check_same_thread=False)
    c.row_factory = sqlite3.Row
    return c

def init_db():
    with db_lock:
        conn = get_db()
        try:
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS sofa_team_stats (
                    team_id INTEGER, tournament_id INTEGER, season_id INTEGER,
                    goals_scored INTEGER, goals_conceded INTEGER,
                    goals_home INTEGER, goals_away INTEGER,
                    conceded_home INTEGER, conceded_away INTEGER,
                    matches INTEGER, matches_home INTEGER, matches_away INTEGER,
                    big_chances INTEGER, shots_on_target INTEGER, shots INTEGER,
                    big_chances_conceded INTEGER, shots_on_target_conceded INTEGER,
                    wins INTEGER, draws INTEGER, losses INTEGER,
                    over15_count INTEGER, over25_count INTEGER,
                    updated_at TEXT,
                    PRIMARY KEY (team_id, tournament_id, season_id)
                );
                CREATE TABLE IF NOT EXISTS sofa_events_cache (
                    date TEXT PRIMARY KEY, data TEXT, updated_at TEXT
                );
                CREATE TABLE IF NOT EXISTS sofa_match_stats (
                    event_id INTEGER PRIMARY KEY,
                    home_shots INTEGER, away_shots INTEGER,
                    home_sot INTEGER, away_sot INTEGER,
                    home_goals INTEGER, away_goals INTEGER,
                    updated_at TEXT
                );
                CREATE TABLE IF NOT EXISTS request_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts TEXT, endpoint TEXT, duration_ms INTEGER,
                    picks_found INTEGER, multiples_built INTEGER
                );
            """)
            conn.commit()
        finally:
            conn.close()

init_db()

# â”€â”€ Poisson + Dixon-Coles (matrice normalizzata) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def dc_tau(x, y, lh, la, rho=-0.13):
    if x == 0 and y == 0: return max(0.001, 1 - lh * la * rho)
    if x == 0 and y == 1: return max(0.001, 1 + lh * rho)
    if x == 1 and y == 0: return max(0.001, 1 + la * rho)
    if x == 1 and y == 1: return max(0.001, 1 - rho)
    return 1.0

def pmf(lam, k):
    if lam <= 0: return 0.0
    return math.exp(k * math.log(lam) - lam - sum(math.log(i) for i in range(1, k + 1)))

def calc_probs(lh, la):
    """Matrice DC normalizzata: la somma post-tau != 1, quindi normalizziamo."""
    matrix = [
        [pmf(lh, h) * pmf(la, a) * dc_tau(h, a, lh, la) for a in range(9)]
        for h in range(9)
    ]
    total = sum(v for row in matrix for v in row) or 1.0
    o15 = o25 = gg = 0.0
    for h in range(9):
        for a in range(9):
            p = matrix[h][a] / total
            t = h + a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if h > 0 and a > 0: gg += p
    return {"over15": min(o15, .99), "over25": min(o25, .99), "gg": min(gg, .99)}

# â”€â”€ Modelli statistici â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def regress(observed, avg, n, k=REGRESSION_K):
    return (n * observed + k * avg) / (n + k)

def calc_xg(stats, per_game=True):
    if not stats: return LEAGUE_AVG
    m    = max(stats.get("matches") or 1, 1)
    bc   = (stats.get("big_chances") or 0) / m
    sot  = (stats.get("shots_on_target") or 0) / m
    soff = max((stats.get("shots") or 0) / m - sot, 0)
    xg   = bc * 0.35 + sot * 0.10 + soff * 0.02
    return regress(xg, LEAGUE_AVG, m) if per_game else xg * m

def calc_xga(stats, per_game=True):
    if not stats: return LEAGUE_AVG
    m   = max(stats.get("matches") or 1, 1)
    bc  = (stats.get("big_chances_conceded") or 0) / m
    sot = (stats.get("shots_on_target_conceded") or 0) / m
    xga = bc * 0.35 + sot * 0.10
    return regress(xga, LEAGUE_AVG, m) if per_game else xga * m

def exp_form(stats):
    if not stats: return 0.5
    m = stats.get("matches") or 0
    if m == 0: return 0.5
    pts = ((stats.get("wins") or 0) * 3 + (stats.get("draws") or 0)) / max(m, 1)
    return min(regress(pts, 1.3, m) / 3, 1.0)

def historical_over(stats, threshold="25"):
    if not stats: return None
    m = stats.get("matches") or 0
    if m < MIN_MATCHES: return None
    count = stats.get(f"over{threshold}_count")
    return (count / m) if count is not None else None

def calc_lambda(hs, as_):
    avg = LEAGUE_AVG
    if hs and as_:
        hm = max(hs.get("matches") or 1, 1)
        am = max(as_.get("matches") or 1, 1)
        att_h = regress((hs.get("goals_home") or 0) / max(hs.get("matches_home") or 1, 1) / avg, 1.0, hm)
        att_a = regress((as_.get("goals_away") or 0) / max(as_.get("matches_away") or 1, 1) / avg, 1.0, am)
        def_h = regress((hs.get("conceded_home") or 0) / max(hs.get("matches_home") or 1, 1) / avg, 1.0, hm)
        def_a = regress((as_.get("conceded_away") or 0) / max(as_.get("matches_away") or 1, 1) / avg, 1.0, am)
        lh_g, la_g = avg * att_h * def_a, avg * att_a * def_h
    elif hs:
        hm = max(hs.get("matches") or 1, 1)
        att_h = regress((hs.get("goals_scored") or 0) / hm / avg, 1.0, hm)
        def_h = regress((hs.get("goals_conceded") or 0) / hm / avg, 1.0, hm)
        lh_g, la_g = avg * att_h, avg * def_h
    elif as_:
        am = max(as_.get("matches") or 1, 1)
        att_a = regress((as_.get("goals_scored") or 0) / am / avg, 1.0, am)
        def_a = regress((as_.get("goals_conceded") or 0) / am / avg, 1.0, am)
        lh_g, la_g = avg * def_a, avg * att_a
    else:
        lh_g = la_g = avg

    lh_xg = calc_xg(hs) * (calc_xga(as_) / avg if as_ else 1.0)
    la_xg = calc_xg(as_) * (calc_xga(hs) / avg if hs else 1.0)

    n      = min((hs.get("matches") or 0) + (as_.get("matches") or 0) if hs and as_ else 0, 60)
    w_g    = min(n / 40, 0.70)
    lh     = lh_g * w_g + lh_xg * (1 - w_g)
    la     = la_g * w_g + la_xg * (1 - w_g)
    lh    *= 0.80 + exp_form(hs) * 0.40
    la    *= 0.80 + exp_form(as_) * 0.40

    lh = max(0.3, min(4.5, lh))
    la = max(0.3, min(4.5, la))

    # Sanity check: se lambda > 3.5 con shot_data assenti, i gol reali sono corrotti.
    # Fallback a xG puro (piÃ¹ robusto con dati scarsi).
    hs_has_shots = hs and ((hs.get("shots") or 0) > 0 or (hs.get("shots_on_target") or 0) > 0)
    as_has_shots = as_ and ((as_.get("shots") or 0) > 0 or (as_.get("shots_on_target") or 0) > 0)
    if (lh > 3.0 or la > 3.0) and not (hs_has_shots or as_has_shots):
        log.warning(f"Lambda sospetto (lh={lh:.2f}, la={la:.2f}) con shot_data assenti â€” fallback xG")
        lh = max(0.3, min(3.0, lh_xg * (0.80 + exp_form(hs) * 0.40)))
        la = max(0.3, min(3.0, la_xg * (0.80 + exp_form(as_) * 0.40)))

    return lh, la

# â”€â”€ SofaScore fetchers con retry + backoff â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def sofa_get(url, timeout=8, retries=2):
    """
    Retry con backoff esponenziale.
    retries=2 â†’ 3 tentativi totali (1 + 2 retry).
    Attese: 1s, 2s (raddoppia ad ogni tentativo).
    """
    for attempt in range(retries + 1):
        try:
            r = requests.get(url, headers=SOFA_HEADERS, timeout=timeout)
            if r.ok:
                return r.json()
            if r.status_code == 429:
                wait = 2 ** attempt
                log.warning(f"Rate limit SofaScore (429), attendo {wait}s â€” {url}")
                time.sleep(wait)
            else:
                log.debug(f"SofaScore HTTP {r.status_code} â€” {url}")
                break  # 4xx non recoverable (tranne 429)
        except requests.Timeout:
            log.warning(f"Timeout tentativo {attempt+1}/{retries+1} â€” {url}")
            if attempt < retries: time.sleep(1.5 ** attempt)
        except Exception as e:
            log.error(f"Errore fetch {url}: {e}")
            break
    return None

def get_team_stats(team_id, t_id, s_id):
    if not all([team_id, t_id, s_id]): return None
    with db_lock:
        conn = get_db()
        try:
            row = conn.execute(
                "SELECT * FROM sofa_team_stats WHERE team_id=? AND tournament_id=? AND season_id=?",
                (team_id, t_id, s_id)
            ).fetchone()
        finally:
            conn.close()

    if row:
        upd = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc) - upd).total_seconds() < 3600 * 12:
            return dict(row)

    data = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/overall")
    if not data:
        log.debug(f"Nessun dato overall per team {team_id}")
        return dict(row) if row else None
    st = data.get("statistics", {})
    if not st: return dict(row) if row else None

    m    = max(st.get("matches") or 1, 1)
    data_h = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/home")
    data_a = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/away")
    st_h_raw = (data_h or {}).get("statistics", {})
    st_a_raw = (data_a or {}).get("statistics", {})
    gs       = st.get("goalsScored") or 0
    gc       = st.get("goalsConceded") or 0

    # FIX CRITICO: SofaScore per leghe basse (es. Scottish L2) restituisce
    # matches_home=0. Con max(0,1)=1 â†’ goals_home/1 invece di goals_home/14
    # â†’ att_h gonfiato 14x â†’ lambda clampato a 4.5 â†’ Gol attesi = 9 (4.5+4.5)
    # â†’ entrambe le squadre della stessa lega â†’ statistiche identiche.
    mh_raw = st_h_raw.get("matches") or 0
    ma_raw = st_a_raw.get("matches") or 0
    st_h   = st_h_raw if mh_raw >= 3 else {}   # dati home non affidabili se < 3
    st_a   = st_a_raw if ma_raw >= 3 else {}   # dati away non affidabili se < 3
    mh     = mh_raw if mh_raw >= 3 else max(m // 2, 1)
    ma     = ma_raw if ma_raw >= 3 else max(m // 2, 1)
    if mh_raw < 3:
        log.debug(f"Team {team_id}: matches_home={mh_raw} insufficienti, fallback mh={mh}")

    rec = {
        "team_id": team_id, "tournament_id": t_id, "season_id": s_id,
        "goals_scored": gs, "goals_conceded": gc,
        "goals_home": st_h.get("goalsScored") if st_h else gs // 2,
        "goals_away": st_a.get("goalsScored") if st_a else gs // 2,
        "conceded_home": st_h.get("goalsConceded") if st_h else gc // 2,
        "conceded_away": st_a.get("goalsConceded") if st_a else gc // 2,
        "matches": m, "matches_home": mh, "matches_away": ma,
        "big_chances": st.get("bigChances") or 0,
        "shots_on_target": st.get("shotsOnTarget") or 0,
        "shots": st.get("shots") or 0,
        "big_chances_conceded": st.get("bigChancesConceded") or 0,
        "shots_on_target_conceded": st.get("shotsOnTargetAgainst") or 0,
        "wins": st.get("wins") or 0,
        "draws": st.get("draws") or 0,
        "losses": st.get("losses") or 0,
        "over15_count": None,
        "over25_count": None,
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }

    with db_lock:
        conn = get_db()
        try:
            conn.execute("""
                INSERT OR REPLACE INTO sofa_team_stats VALUES
                (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            """, list(rec.values()))
            conn.commit()
        finally:
            conn.close()
    return rec

def get_event_odds(event_id):
    data = sofa_get(f"https://api.sofascore.com/api/v1/event/{event_id}/odds/1/all")
    if not data: return {}
    odds = {}
    for mkt in data.get("markets", []):
        for ch in mkt.get("choices", []):
            name = ch.get("name", "")
            frac = ch.get("fractionalValue") or ch.get("initialFractionalValue")
            try:
                if frac and "/" in str(frac):
                    n, d = str(frac).split("/")
                    dec  = round(int(n) / int(d) + 1, 3)
                    if dec > 1: odds[name] = dec
            except Exception:
                pass
    return odds

def get_today_events(date_str):
    with db_lock:
        conn = get_db()
        try:
            row = conn.execute(
                "SELECT data, updated_at FROM sofa_events_cache WHERE date=?", (date_str,)
            ).fetchone()
        finally:
            conn.close()

    if row:
        upd = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc) - upd).total_seconds() < 3600 * 2:
            return json.loads(row["data"])

    data = sofa_get(f"https://api.sofascore.com/api/v1/sport/football/scheduled-events/{date_str}", timeout=15)
    if not data:
        log.warning(f"Nessun evento da SofaScore per {date_str}")
        return []
    events = data.get("events", [])
    log.info(f"SofaScore: {len(events)} eventi trovati per {date_str}")

    with db_lock:
        conn = get_db()
        try:
            conn.execute(
                "INSERT OR REPLACE INTO sofa_events_cache (date,data,updated_at) VALUES (?,?,?)",
                (date_str, json.dumps(events), datetime.now(timezone.utc).isoformat())
            )
            conn.commit()
        finally:
            conn.close()
    return events

FLAG_MAP = {
    "england": "ðŸ´ó §ó ¢ó ¥ó ®ó §ó ¿", "italy": "ðŸ‡®ðŸ‡¹", "spain": "ðŸ‡ªðŸ‡¸", "germany": "ðŸ‡©ðŸ‡ª",
    "france": "ðŸ‡«ðŸ‡·", "portugal": "ðŸ‡µðŸ‡¹", "netherlands": "ðŸ‡³ðŸ‡±", "brazil": "ðŸ‡§ðŸ‡·",
    "argentina": "ðŸ‡¦ðŸ‡·", "usa": "ðŸ‡ºðŸ‡¸", "turkey": "ðŸ‡¹ðŸ‡·", "greece": "ðŸ‡¬ðŸ‡·",
    "belgium": "ðŸ‡§ðŸ‡ª", "scotland": "ðŸ´ó §ó ¢ó ³ó £ó ´ó ¿ SCO", "austria": "ðŸ‡¦ðŸ‡¹",
    "switzerland": "ðŸ‡¨ðŸ‡­", "mexico": "ðŸ‡²ðŸ‡½", "japan": "ðŸ‡¯ðŸ‡µ", "south-korea": "ðŸ‡°ðŸ‡·",
}

def analyze_event(ev, start_utc, end_utc):
    ct = ev.get("startTimestamp")
    if not ct: return []
    ev_time = datetime.fromtimestamp(ct, tz=timezone.utc)
    if not (start_utc <= ev_time <= end_utc): return []
    if ev.get("status", {}).get("type", "") in ["inprogress", "finished", "postponed", "canceled"]:
        return []

    ht  = ev.get("homeTeam", {}); at = ev.get("awayTeam", {})
    hn  = ht.get("name", "");     an = at.get("name", "")
    hid = ht.get("id");           aid = at.get("id")
    eid = ev.get("id")
    tourn = ev.get("tournament", {})
    ut    = tourn.get("uniqueTournament", {})
    t_id  = ut.get("id"); s_id = ev.get("season", {}).get("id")
    lg    = tourn.get("name", "")
    flag  = FLAG_MAP.get(tourn.get("category", {}).get("flag", "").lower(), "âš½")

    hs  = get_team_stats(hid, t_id, s_id)
    as_ = get_team_stats(aid, t_id, s_id)
    if not (hs or as_):
        log.debug(f"Skip {hn} vs {an}: nessun dato squadre")
        return []

    lh, la = calc_lambda(hs, as_)
    pr     = calc_probs(lh, la)
    fh     = round(exp_form(hs), 2)
    fa     = round(exp_form(as_), 2)
    odds_data = get_event_odds(eid)

    hist_o25_h = historical_over(hs, "25")
    hist_o25_a = historical_over(as_, "25")
    hist_conf  = round((hist_o25_h + hist_o25_a) / 2, 3) if (hist_o25_h and hist_o25_a) else None

    picks = []

    o15 = odds_data.get("Over 1.5") or odds_data.get("Over1.5")
    if o15 and 1.10 <= o15 <= 1.65:
        prob = min(pr["over15"] * 1.05, 0.99) if (hist_conf and hist_conf > 0.60) else pr["over15"]
        picks.append({"name": "Over 1.5", "odds": round(o15, 2), "prob": round(prob, 3),
                      "edge": round(prob - 1/o15, 3), "market": "over15"})

    o25 = odds_data.get("Over 2.5") or odds_data.get("Over2.5")
    if o25 and 1.35 <= o25 <= 2.60:
        prob = min(pr["over25"] * 1.04, 0.99) if (hist_conf and hist_conf > 0.50) else pr["over25"]
        picks.append({"name": "Over 2.5", "odds": round(o25, 2), "prob": round(prob, 3),
                      "edge": round(prob - 1/o25, 3), "market": "over25"})

    # GG: solo quota reale di mercato
    gg_odds = odds_data.get("Yes") or odds_data.get("GG")
    if gg_odds and 1.40 <= gg_odds <= 2.50:
        prob = pr["gg"]
        picks.append({"name": "Goal/Goal", "odds": round(gg_odds, 2), "prob": round(prob, 3),
                      "edge": round(prob - 1/gg_odds, 3), "market": "gg"})

    if not picks: return []

    # QualitÃ  dato: bassa se shot_data assenti (leghe basse senza stats SofaScore)
    has_shots_h = (hs.get("shots") or 0) > 0 or (hs.get("shots_on_target") or 0) > 0 if hs else False
    has_shots_a = (as_.get("shots") or 0) > 0 or (as_.get("shots_on_target") or 0) > 0 if as_ else False
    data_quality = "high" if (has_shots_h and has_shots_a) else "medium" if (has_shots_h or has_shots_a) else "low"
    if data_quality == "low":
        log.info(f"[LOW QUALITY] {hn} vs {an} â€” nessun dato shot, lambda basato su soli gol/forma")

    base = {
        "match": f"{hn} vs {an}", "league": f"{flag} {lg}",
        "commence_time": ev_time.isoformat(),
        "probs": pr, "exp_g": round(lh + la, 2),
        "lambda_home": round(lh, 3), "lambda_away": round(la, 3),
        "home_form": fh, "away_form": fa,
        "has_real_stats": True, "hist_over25": hist_conf,
        "data_quality": data_quality,
    }
    return [{**base, **p, "score": p["edge"]*50 + p["prob"]*30 + (fh+fa)*10 + 15} for p in picks]

# â”€â”€ Combo builder ibrido â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
def greedy_combo(picks, target, cfg):
    """
    Greedy beam search per target alti (>10).
    Parte dal pick migliore e aggiunge iterativamente quello
    che avvicina di piÃ¹ la quota al target minimizzando la distanza log.
    Molto piÃ¹ veloce del brute-force per cfg["max_picks"] >= 6.
    """
    log_target = math.log(max(target, 1.01))
    candidates = sorted(picks, key=lambda p: p["score"], reverse=True)[:30]
    beam = [[p] for p in candidates[:10]]  # 10 semi iniziali

    for _ in range(cfg["max_picks"] - 1):
        new_beam = []
        for current in beam:
            current_log = sum(math.log(p["odds"]) for p in current)
            remaining   = log_target - current_log
            if remaining <= 0: continue
            current_matches = {p["match"] for p in current}
            for cand in candidates:
                if cand["match"] in current_matches: continue
                if math.log(cand["odds"]) > remaining * 1.5: continue
                new_combo = current + [cand]
                mc = {}
                for p in new_combo: mc[p["market"]] = mc.get(p["market"], 0) + 1
                if any(v > 2 for v in mc.values()): continue
                new_beam.append(new_combo)
        if not new_beam: break
        beam = sorted(new_beam, key=lambda c: (
            math.prod(p["prob"] for p in c) * 70
            + sum(p["edge"] for p in c) * 15
            - abs(sum(math.log(p["odds"]) for p in c) - log_target) * 15
        ), reverse=True)[:15]  # mantieni top-15

    valid = [
        c for c in beam
        if cfg["min_picks"] <= len(c) <= cfg["max_picks"]
        and len({p["match"] for p in c}) == len(c)
        and target * 0.55 <= math.prod(p["odds"] for p in c) <= target * 1.55
    ]
    if not valid: return []
    return max(valid, key=lambda c: math.prod(p["prob"] for p in c))

def find_best_combo(picks, target, cfg):
    """
    Brute-force per target piccoli (<=10, max_picks<=6).
    Greedy beam search per target grandi (100x).
    """
    log_target = math.log(max(target, 1.01))
    for min_edge in [0.03, 0.01, 0.0, -0.05]:
        f = [p for p in picks if p["edge"] >= min_edge]
        if len(f) >= cfg["min_picks"]: break
    if len(f) < cfg["min_picks"]: f = picks

    # Pre-filtro quota singola incompatibile
    f = [p for p in f if math.log(p["odds"]) < log_target * 1.2]

    if target > 10:
        return greedy_combo(f, target, cfg)

    top = sorted(f, key=lambda p: p["score"], reverse=True)[:25]
    best, bs = [], -1
    for sz in range(cfg["min_picks"], cfg["max_picks"] + 1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            if len({p["match"] for p in combo}) != sz: continue
            mc = {}
            for p in combo: mc[p["market"]] = mc.get(p["market"], 0) + 1
            if any(v > 2 for v in mc.values()): continue
            tot = math.prod(p["odds"] for p in combo)
            if tot < target * 0.55 or tot > target * 1.55: continue
            cp = math.prod(p["prob"] for p in combo)
            sc = cp * 70 + sum(p["edge"] for p in combo) * 15 - abs(tot - target) / target * 15
            if sc > bs: bs = sc; best = list(combo)
        if best and abs(math.prod(p["odds"] for p in best) - target) / target < 0.15:
            break
    return best

# â”€â”€ Routes â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
@app.route("/health")
def health():
    with db_lock:
        conn = get_db()
        try:
            sc = conn.execute("SELECT COUNT(*) as c FROM sofa_team_stats").fetchone()["c"]
            ec = conn.execute("SELECT COUNT(*) as c FROM sofa_events_cache").fetchone()["c"]
            rl = conn.execute("SELECT COUNT(*) as c FROM request_log").fetchone()["c"]
        finally:
            conn.close()
    return jsonify({"status": "ok", "team_stats_cached": sc, "events_cached": ec, "requests_logged": rl})

@app.route("/picks")
def picks_debug():
    """
    Endpoint di debug: restituisce tutti i pick disponibili per una data
    senza costruire multiple. Utile per ispezionare lambda, prob, edge.
    Query param: ?date=YYYY-MM-DD (default: oggi)
    """
    date_str = request.args.get("date") or datetime.now(ITALY_TZ).strftime("%Y-%m-%d")
    try:
        day_dt = datetime.strptime(date_str, "%Y-%m-%d").replace(tzinfo=ITALY_TZ)
    except ValueError:
        return jsonify({"error": "Formato data non valido. Usa YYYY-MM-DD"}), 400

    start = day_dt.astimezone(timezone.utc)
    end   = (day_dt.replace(hour=23, minute=59, second=59)).astimezone(timezone.utc)
    events = get_today_events(date_str)

    all_picks = []
    with ThreadPoolExecutor(max_workers=10) as ex:
        futures = {ex.submit(analyze_event, ev, start, end): ev for ev in events}
        for fut in as_completed(futures):
            try: all_picks.extend(fut.result())
            except Exception as e: log.error(f"analyze_event error: {e}")

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen: seen.add(k); unique.append(p)

    unique.sort(key=lambda p: p["score"], reverse=True)
    return jsonify({
        "date": date_str,
        "total_picks": len(unique),
        "value_bets": sum(1 for p in unique if p["edge"] > 0.02),
        "picks": unique[:50],  # max 50 nel debug
    })

@app.route("/generate", methods=["POST"])
@timed
def generate():
    t0       = time.perf_counter()
    now_utc  = datetime.now(timezone.utc)
    now_it   = now_utc.astimezone(ITALY_TZ)

    all_picks, day_offset = [], 0
    for day_offset in range(3):
        day_dt   = now_it.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start    = now_utc if day_offset == 0 else day_dt.astimezone(timezone.utc)
        end      = (now_it.replace(hour=23, minute=59, second=59) + timedelta(days=day_offset)).astimezone(timezone.utc)

        events = get_today_events(date_str)
        log.info(f"Analisi {len(events)} eventi per {date_str} (day_offset={day_offset})")

        day_picks = []
        with ThreadPoolExecutor(max_workers=10) as ex:
            futures = {ex.submit(analyze_event, ev, start, end): ev for ev in events}
            for fut in as_completed(futures):
                try: day_picks.extend(fut.result())
                except Exception as e: log.error(f"analyze_event error: {e}")

        if day_picks:
            all_picks = day_picks
            break

    if not all_picks:
        return jsonify({"error": "Nessuna partita trovata con dati statistici nei prossimi 3 giorni."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen: seen.add(k); unique.append(p)

    day_label  = "dopodomani" if day_offset == 2 else "domani" if day_offset == 1 else "oggi"
    multiples, used = [], set()

    for tgt in [3, 5, 8, 10, 100]:
        cfg   = get_cfg(tgt)
        avail = [p for p in unique if p["match"] not in used] or unique
        combo = find_best_combo(avail, tgt, cfg)
        if combo:
            for p in combo: used.add(p["match"])
            multiples.append({
                "target": tgt,
                "total_odds": round(math.prod(p["odds"] for p in combo), 2),
                "combo_probability": round(math.prod(p["prob"] for p in combo) * 100, 1),
                "picks": combo,
                "value_in_combo": sum(1 for p in combo if p["edge"] > 0.02),
            })
            log.info(f"Multipla {tgt}x: {len(combo)} pick, quota {round(math.prod(p['odds'] for p in combo),2)}")

    if not multiples:
        return jsonify({"error": "Impossibile costruire multipla."}), 404

    duration_ms = int((time.perf_counter() - t0) * 1000)
    with db_lock:
        conn = get_db()
        try:
            conn.execute(
                "INSERT INTO request_log (ts,endpoint,duration_ms,picks_found,multiples_built) VALUES (?,?,?,?,?)",
                (now_utc.isoformat(), "/generate", duration_ms, len(unique), len(multiples))
            )
            conn.commit()
        finally:
            conn.close()

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "leagues_with_data": len({p["league"] for p in unique}),
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": sum(1 for p in unique if p["edge"] > 0.02),
        "duration_ms": duration_ms,
        "source": "sofascore",
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)