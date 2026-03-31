# -*- coding: utf-8 -*-
from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, os, sqlite3, threading, json, logging, time
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import wraps

# -- Logging --
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler("scommettiamo.log", encoding="utf-8"),
    ],
)
log = logging.getLogger("scommettiamo")

app = Flask(__name__)
CORS(app)

DB_PATH      = os.path.join(os.path.dirname(os.path.abspath(__file__)), "scommettiamo.db")
db_lock      = threading.Lock()
ITALY_TZ     = ZoneInfo("Europe/Rome")
LEAGUE_AVG   = 1.35
MIN_MATCHES  = 5
REGRESSION_K = 10

# API Keys da variabili d'ambiente (non nel codice)
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")  # fallback env var

def get_odds_api_key(req):
    """Prende la key dall'header X-Odds-Key o dalla variabile d'ambiente."""
    return req.headers.get("X-Odds-Key", "") or ODDS_API_KEY

SOFA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Accept": "application/json",
    "Referer": "https://www.sofascore.com/",
}

# -- Timing --
def timed(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        t0 = time.perf_counter()
        result = fn(*a, **kw)
        log.info(f"{fn.__name__} in {time.perf_counter()-t0:.2f}s")
        return result
    return wrapper

# -- Database --
def get_db():
    c = sqlite3.connect(DB_PATH, check_same_thread=False)
    c.row_factory = sqlite3.Row
    return c

def init_db():
    sql = (
        "CREATE TABLE IF NOT EXISTS sofa_team_stats ("
        "team_id INTEGER, tournament_id INTEGER, season_id INTEGER,"
        "goals_scored INTEGER, goals_conceded INTEGER,"
        "goals_home INTEGER, goals_away INTEGER,"
        "conceded_home INTEGER, conceded_away INTEGER,"
        "matches INTEGER, matches_home INTEGER, matches_away INTEGER,"
        "big_chances INTEGER, shots_on_target INTEGER, shots INTEGER,"
        "big_chances_conceded INTEGER, shots_on_target_conceded INTEGER,"
        "wins INTEGER, draws INTEGER, losses INTEGER,"
        "over15_count INTEGER, over25_count INTEGER, updated_at TEXT,"
        "PRIMARY KEY (team_id, tournament_id, season_id));"
        "CREATE TABLE IF NOT EXISTS sofa_events_cache "
        "(date TEXT PRIMARY KEY, data TEXT, updated_at TEXT);"
        "CREATE TABLE IF NOT EXISTS odds_cache "
        "(sport TEXT, date TEXT, data TEXT, updated_at TEXT,"
        "PRIMARY KEY (sport, date));"
    )
    with db_lock:
        conn = get_db()
        try:
            conn.executescript(sql)
            conn.commit()
        finally:
            conn.close()

init_db()

# ============================================================
# POISSON + DIXON-COLES
# ============================================================
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
    """Calcola probabilità match completo + primo tempo stimato."""
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

    # Over 0.5 primo tempo: ~45% dei gol cadono nel 1T
    # P(almeno 1 gol in 1T) = 1 - P(0 gol in 1T) = 1 - e^(-lambda_1T)
    lambda_1t = (lh + la) * 0.45
    o05_1t = 1.0 - math.exp(-lambda_1t)

    return {
        "over15":   min(o15, .99),
        "over25":   min(o25, .99),
        "gg":       min(gg,  .99),
        "over05_1t": min(o05_1t, .99),
    }

# ============================================================
# MODELLI STATISTICI
# ============================================================
def regress(observed, avg, n, k=REGRESSION_K):
    return (n * observed + k * avg) / (n + k)

def calc_xg(stats):
    if not stats: return LEAGUE_AVG
    m   = max(stats.get("matches") or 1, 1)
    bc  = (stats.get("big_chances") or 0) / m
    sot = (stats.get("shots_on_target") or 0) / m
    soff= max((stats.get("shots") or 0) / m - sot, 0)
    if (stats.get("shots") or 0) > 0 or sot > 0:
        xg = bc * 0.35 + sot * 0.10 + soff * 0.02
    else:
        xg = (stats.get("goals_scored") or 0) / m
    return regress(xg, LEAGUE_AVG, m)

def calc_xga(stats):
    if not stats: return LEAGUE_AVG
    m   = max(stats.get("matches") or 1, 1)
    bc  = (stats.get("big_chances_conceded") or 0) / m
    sot = (stats.get("shots_on_target_conceded") or 0) / m
    if (stats.get("shots_on_target_conceded") or 0) > 0 or bc > 0:
        xga = bc * 0.35 + sot * 0.10
    else:
        xga = (stats.get("goals_conceded") or 0) / m
    return regress(xga, LEAGUE_AVG, m)

def exp_form(stats):
    if not stats: return 0.5
    m = stats.get("matches") or 0
    if m == 0: return 0.5
    pts = ((stats.get("wins") or 0) * 3 + (stats.get("draws") or 0)) / max(m, 1)
    return min(regress(pts, 1.3, m) / 3, 1.0)

def calc_lambda(hs, as_):
    avg = LEAGUE_AVG
    if hs and as_:
        hm    = max(hs.get("matches") or 1, 1)
        am    = max(as_.get("matches") or 1, 1)
        att_h = regress((hs.get("goals_home") or 0) / max(hs.get("matches_home") or 1, 1) / avg, 1.0, hm)
        att_a = regress((as_.get("goals_away") or 0) / max(as_.get("matches_away") or 1, 1) / avg, 1.0, am)
        def_h = regress((hs.get("conceded_home") or 0) / max(hs.get("matches_home") or 1, 1) / avg, 1.0, hm)
        def_a = regress((as_.get("conceded_away") or 0) / max(as_.get("matches_away") or 1, 1) / avg, 1.0, am)
        lh_g, la_g = avg * att_h * def_a, avg * att_a * def_h
    elif hs:
        hm    = max(hs.get("matches") or 1, 1)
        att_h = regress((hs.get("goals_scored") or 0) / hm / avg, 1.0, hm)
        def_h = regress((hs.get("goals_conceded") or 0) / hm / avg, 1.0, hm)
        lh_g, la_g = avg * att_h, avg * def_h
    elif as_:
        am    = max(as_.get("matches") or 1, 1)
        att_a = regress((as_.get("goals_scored") or 0) / am / avg, 1.0, am)
        def_a = regress((as_.get("goals_conceded") or 0) / am / avg, 1.0, am)
        lh_g, la_g = avg * def_a, avg * att_a
    else:
        lh_g = la_g = avg

    lh_xg = calc_xg(hs) * (calc_xga(as_) / avg if as_ else 1.0)
    la_xg = calc_xg(as_) * (calc_xga(hs) / avg if hs else 1.0)
    n     = min((hs.get("matches") or 0) + (as_.get("matches") or 0) if hs and as_ else 0, 60)
    w_g   = min(n / 40, 0.70)
    lh    = lh_g * w_g + lh_xg * (1 - w_g)
    la    = la_g * w_g + la_xg * (1 - w_g)
    lh   *= 0.92 + exp_form(hs) * 0.20
    la   *= 0.92 + exp_form(as_) * 0.20
    lh    = max(0.3, min(4.5, lh))
    la    = max(0.3, min(4.5, la))
    return lh, la

# ============================================================
# SOFASCORE - solo statistiche squadre
# ============================================================
def sofa_get(url, timeout=8, retries=2):
    for attempt in range(retries + 1):
        try:
            r = requests.get(url, headers=SOFA_HEADERS, timeout=timeout)
            if r.ok: return r.json()
            if r.status_code == 429:
                time.sleep(2 ** attempt)
            else:
                break
        except requests.Timeout:
            if attempt < retries: time.sleep(1.5 ** attempt)
        except Exception as e:
            log.error(f"sofa_get error {url}: {e}"); break
    return None

def _poisson_over_count(total_goals, matches, threshold):
    if not matches or matches < 1: return None
    avg = total_goals / matches
    if avg <= 0: return None
    k = int(threshold)
    p_under = sum(math.exp(-avg) * avg**i / math.factorial(i) for i in range(k + 1))
    return round(max(0.0, 1.0 - p_under) * matches)

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
    if not data: return dict(row) if row else None
    st = data.get("statistics", {})
    if not st: return dict(row) if row else None
    m      = max(st.get("matches") or 1, 1)
    data_h = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/home")
    data_a = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/away")
    st_h_raw = (data_h or {}).get("statistics", {})
    st_a_raw = (data_a or {}).get("statistics", {})
    gs = st.get("goalsScored") or 0
    gc = st.get("goalsConceded") or 0
    mh_raw = st_h_raw.get("matches") or 0
    ma_raw = st_a_raw.get("matches") or 0
    st_h = st_h_raw if mh_raw >= 3 else {}
    st_a = st_a_raw if ma_raw >= 3 else {}
    mh = mh_raw if mh_raw >= 3 else max(m // 2, 1)
    ma = ma_raw if ma_raw >= 3 else max(m // 2, 1)
    rec = {
        "team_id": team_id, "tournament_id": t_id, "season_id": s_id,
        "goals_scored": gs, "goals_conceded": gc,
        "goals_home":    st_h.get("goalsScored")   if st_h else gs // 2,
        "goals_away":    st_a.get("goalsScored")   if st_a else gs // 2,
        "conceded_home": st_h.get("goalsConceded") if st_h else gc // 2,
        "conceded_away": st_a.get("goalsConceded") if st_a else gc // 2,
        "matches": m, "matches_home": mh, "matches_away": ma,
        "big_chances":              st.get("bigChances") or 0,
        "shots_on_target":          st.get("shotsOnTarget") or 0,
        "shots":                    st.get("shots") or 0,
        "big_chances_conceded":     st.get("bigChancesConceded") or 0,
        "shots_on_target_conceded": st.get("shotsOnTargetAgainst") or 0,
        "wins":   st.get("wins") or 0,
        "draws":  st.get("draws") or 0,
        "losses": st.get("losses") or 0,
        "over15_count": _poisson_over_count(gs + gc, m, 1.5),
        "over25_count": _poisson_over_count(gs + gc, m, 2.5),
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }
    with db_lock:
        conn = get_db()
        try:
            conn.execute(
                "INSERT OR REPLACE INTO sofa_team_stats VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                list(rec.values()))
            conn.commit()
        finally:
            conn.close()
    return rec

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
        log.warning(f"Nessun evento SofaScore per {date_str}")
        return []
    events = data.get("events", [])
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

# ============================================================
# THE ODDS API - quote reali
# ============================================================
ODDS_SPORTS = [
    "soccer_italy_serie_a",
    "soccer_italy_serie_b",
    "soccer_england_league1",
    "soccer_england_league2",
    "soccer_epl",
    "soccer_spain_la_liga",
    "soccer_germany_bundesliga",
    "soccer_france_ligue_one",
    "soccer_portugal_primeira_liga",
    "soccer_turkey_super_league",
    "soccer_netherlands_eredivisie",
    "soccer_belgium_first_div",
]

def get_odds_api(sport, date_str, api_key=""):
    """Recupera quote da The Odds API con cache 2h."""
    key = api_key or ODDS_API_KEY
    with db_lock:
        conn = get_db()
        try:
            row = conn.execute(
                "SELECT data, updated_at FROM odds_cache WHERE sport=? AND date=?",
                (sport, date_str)
            ).fetchone()
        finally:
            conn.close()
    if row:
        upd = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc) - upd).total_seconds() < 3600 * 2:
            return json.loads(row["data"])

    if not key:
        log.warning("ODDS_API_KEY non configurata")
        return []

    # commenceTimeTo = fine giornata
    try:
        day_start = f"{date_str}T00:00:00Z"
        day_end   = f"{date_str}T23:59:59Z"
        url = (
            f"https://api.the-odds-api.com/v4/sports/{sport}/odds/"
            f"?apiKey={key}"
            f"&regions=eu"
            f"&markets=h2h,totals,team_totals"
            f"&oddsFormat=decimal"
            f"&commenceTimeFrom={day_start}"
            f"&commenceTimeTo={day_end}"
            f"&bookmakers=unibet_eu,bet365,pinnacle,betfair_ex_eu"
        )
        r = requests.get(url, timeout=10)
        remaining = r.headers.get("x-requests-remaining", "?")
        log.info(f"[OddsAPI] {sport}: HTTP {r.status_code}, remaining={remaining}")
        if not r.ok:
            log.warning(f"[OddsAPI] {sport}: {r.status_code} {r.text[:200]}")
            return []
        data = r.json()
        with db_lock:
            conn = get_db()
            try:
                conn.execute(
                    "INSERT OR REPLACE INTO odds_cache (sport,date,data,updated_at) VALUES (?,?,?,?)",
                    (sport, date_str, json.dumps(data), datetime.now(timezone.utc).isoformat())
                )
                conn.commit()
            finally:
                conn.close()
        return data
    except Exception as e:
        log.error(f"[OddsAPI] errore {sport}: {e}")
        return []

def fetch_all_odds(date_str, api_key=""):
    """Recupera quote da tutti i campionati in parallelo."""
    all_games = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futures = {ex.submit(get_odds_api, sport, date_str, api_key): sport for sport in ODDS_SPORTS}
        for fut in as_completed(futures):
            try:
                games = fut.result()
                all_games.extend(games)
            except Exception as e:
                log.error(f"fetch_all_odds error: {e}")
    log.info(f"[OddsAPI] totale partite con quote: {len(all_games)}")
    return all_games

def parse_game_odds(game):
    """
    Estrae da un game OddsAPI:
    - quota casa, quota ospite (h2h)
    - quota Over 0.5 1T (first_half_totals o team_totals)
    Restituisce dict o None.
    """
    home = game.get("home_team", "")
    away = game.get("away_team", "")
    ct   = game.get("commence_time", "")

    odds_h2h    = {"home": None, "away": None, "draw": None}
    odds_o05_1t = None

    for bk in game.get("bookmakers", []):
        for mkt in bk.get("markets", []):
            key = mkt.get("key", "")

            # H2H - quota casa/ospite
            if key == "h2h" and not odds_h2h["home"]:
                for oc in mkt.get("outcomes", []):
                    n = oc.get("name", "")
                    p = oc.get("price")
                    if n == home:   odds_h2h["home"] = p
                    elif n == away: odds_h2h["away"] = p
                    elif n == "Draw": odds_h2h["draw"] = p

            # Over 0.5 primo tempo
            # The Odds API usa "h2h_h1" per 1T o "alternate_spreads"
            # ma il mercato più affidabile è totals con point=0.5 sul primo tempo
            if key in ("h2h_h1", "totals_h1", "alternate_totals_h1") and not odds_o05_1t:
                for oc in mkt.get("outcomes", []):
                    if oc.get("name") == "Over" and oc.get("point") == 0.5:
                        odds_o05_1t = oc.get("price")

        # se già trovato tutto, esci
        if odds_h2h["home"] and odds_o05_1t:
            break

    return {
        "home":       home,
        "away":       away,
        "commence":   ct,
        "odds_home":  odds_h2h["home"],
        "odds_away":  odds_h2h["away"],
        "odds_draw":  odds_h2h["draw"],
        "odds_o05_1t": odds_o05_1t,
    }

def normalize_name(name):
    """Normalizzazione base per match fuzzy tra SofaScore e OddsAPI."""
    import unicodedata
    name = unicodedata.normalize("NFD", name.lower())
    name = "".join(c for c in name if unicodedata.category(c) != "Mn")
    name = name.replace("fc ", "").replace(" fc", "").replace("afc ", "").replace(" afc", "")
    name = name.replace(".", "").replace("-", " ").strip()
    return name

def match_teams(sofa_home, sofa_away, odds_home, odds_away):
    """Verifica se due partite sono la stessa (tolleranza sui nomi)."""
    sh = normalize_name(sofa_home)
    sa = normalize_name(sofa_away)
    oh = normalize_name(odds_home)
    oa = normalize_name(odds_away)
    # match esatto o parziale (almeno 4 char in comune)
    def sim(a, b):
        return a == b or a in b or b in a or (len(a) >= 4 and a[:4] == b[:4])
    return sim(sh, oh) and sim(sa, oa)

FLAG_MAP = {
    "england": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "italy": "🇮🇹", "spain": "🇪🇸",
    "germany": "🇩🇪", "france": "🇫🇷", "portugal": "🇵🇹",
    "netherlands": "🇳🇱", "brazil": "🇧🇷", "argentina": "🇦🇷",
    "usa": "🇺🇸", "turkey": "🇹🇷", "greece": "🇬🇷",
    "belgium": "🇧🇪", "scotland": "🏴󠁧󠁢󠁳󠁣󠁴󠁿",
    "austria": "🇦🇹", "switzerland": "🇨🇭",
}

# ============================================================
# ENDPOINT PRINCIPALE: /over05-1t
# ============================================================
@app.route("/over05-1t")
@timed
def over05_1t():
    """
    Sistema Over 0.5 1T per squadre ospiti quotate 2.6-3.2.

    Query params:
        away_min  float  default 2.6   (quota minima squadra ospite)
        away_max  float  default 3.2   (quota massima squadra ospite)
        date      str    YYYY-MM-DD    (opzionale, default oggi/domani)
    """
    AWAY_MIN = float(request.args.get("away_min", 2.6))
    AWAY_MAX = float(request.args.get("away_max", 3.2))
    date_req = request.args.get("date")
    now_utc  = datetime.now(timezone.utc)
    now_it   = now_utc.astimezone(ITALY_TZ)

    results  = []
    used_date = None
    day_label = "oggi"

    for day_offset in range(3):
        day_dt   = now_it.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)
        date_str = date_req if date_req else day_dt.strftime("%Y-%m-%d")
        start    = day_dt.astimezone(timezone.utc)
        end      = day_dt.replace(hour=23, minute=59, second=59).astimezone(timezone.utc)

        # 1. Scarica eventi SofaScore
        events = get_today_events(date_str)
        log.info(f"[over05-1t] {len(events)} eventi SofaScore per {date_str}")

        # 2. Scarica quote da OddsAPI
        odds_games = fetch_all_odds(date_str, api_key=get_odds_api_key(request))
        log.info(f"[over05-1t] {len(odds_games)} partite con quote OddsAPI")

        # 3. Analizza ogni evento SofaScore
        day_results = []
        for ev in events:
            ct = ev.get("startTimestamp")
            if not ct: continue
            ev_time = datetime.fromtimestamp(ct, tz=timezone.utc)
            if ev.get("status", {}).get("type", "") in ("inprogress", "finished", "postponed", "canceled"):
                continue
            if not (start <= ev_time <= end): continue

            ht  = ev.get("homeTeam", {}); at = ev.get("awayTeam", {})
            hn  = ht.get("name", "");    an = at.get("name", "")
            hid = ht.get("id");          aid = at.get("id")
            tourn = ev.get("tournament", {})
            ut    = tourn.get("uniqueTournament", {})
            t_id  = ut.get("id"); s_id = ev.get("season", {}).get("id")
            lg    = tourn.get("name", "")
            flag  = FLAG_MAP.get(tourn.get("category", {}).get("flag", "").lower(), "⚽")

            # 4. Statistiche squadre
            hs  = get_team_stats(hid, t_id, s_id)
            as_ = get_team_stats(aid, t_id, s_id)
            if not (hs or as_): continue

            lh, la = calc_lambda(hs, as_)
            pr = calc_probs(lh, la)

            # 5. Cerca la partita nelle quote OddsAPI
            matched_game = None
            for og in odds_games:
                if match_teams(hn, an, og.get("home_team",""), og.get("away_team","")):
                    matched_game = parse_game_odds(og)
                    break

            if not matched_game:
                continue

            odds_away   = matched_game.get("odds_away")
            odds_o05_1t = matched_game.get("odds_o05_1t")

            # 6. Filtra: quota ospite nel range
            if not odds_away or not (AWAY_MIN <= odds_away <= AWAY_MAX):
                continue

            # 7. Calcola edge su Over 0.5 1T
            prob_o05_1t = pr["over05_1t"]
            edge_o05_1t = None
            if odds_o05_1t and odds_o05_1t > 1:
                edge_o05_1t = round(prob_o05_1t - 1 / odds_o05_1t, 3)

            has_shots_h = (hs.get("shots") or 0) > 0 if hs else False
            has_shots_a = (as_.get("shots") or 0) > 0 if as_ else False
            data_quality = "high" if (has_shots_h and has_shots_a) else "medium" if (has_shots_h or has_shots_a) else "low"

            day_results.append({
                "match":          f"{hn} vs {an}",
                "league":         f"{flag} {lg}",
                "commence_time":  ev_time.isoformat(),
                "odds_away":      odds_away,
                "odds_home":      matched_game.get("odds_home"),
                "odds_draw":      matched_game.get("odds_draw"),
                "odds_o05_1t":    odds_o05_1t,
                "prob_o05_1t":    round(prob_o05_1t, 3),
                "prob_o05_1t_pct": f"{round(prob_o05_1t*100, 1)}%",
                "edge_o05_1t":    edge_o05_1t,
                "value":          edge_o05_1t is not None and edge_o05_1t > 0,
                "exp_goals":      round(lh + la, 2),
                "lambda_home":    round(lh, 3),
                "lambda_away":    round(la, 3),
                "data_quality":   data_quality,
            })

        if day_results:
            results = day_results
            used_date = date_str
            day_label = ["oggi", "domani", "dopodomani"][day_offset]
            break
        if date_req: break

    if not results:
        return jsonify({
            "error": f"Nessuna partita trovata con quota ospite {AWAY_MIN}-{AWAY_MAX}.",
            "suggerimento": "Verifica che ODDS_API_KEY sia configurata su Railway come variabile d'ambiente."
        }), 404

    # Ordina: prima le VALUE, poi per probabilità decrescente
    results.sort(key=lambda x: (x["value"], x["prob_o05_1t"]), reverse=True)

    return jsonify({
        "day":            day_label,
        "date":           used_date,
        "away_range":     f"{AWAY_MIN}-{AWAY_MAX}",
        "totale_trovate": len(results),
        "value_picks":    sum(1 for r in results if r["value"]),
        "picks":          results,
    })

# ============================================================
# UTILITY ENDPOINTS
# ============================================================
@app.route("/health")
def health():
    api_ok = bool(get_odds_api_key(request))
    with db_lock:
        conn = get_db()
        try:
            sc = conn.execute("SELECT COUNT(*) as c FROM sofa_team_stats").fetchone()["c"]
            ec = conn.execute("SELECT COUNT(*) as c FROM sofa_events_cache").fetchone()["c"]
            oc = conn.execute("SELECT COUNT(*) as c FROM odds_cache").fetchone()["c"]
        finally:
            conn.close()
    return jsonify({
        "status": "ok",
        "odds_api_configured": api_ok,
        "team_stats_cached": sc,
        "events_cached": ec,
        "odds_cached": oc,
    })

@app.route("/reset-cache", methods=["POST"])
def reset_cache():
    with db_lock:
        conn = get_db()
        try:
            conn.executescript("DELETE FROM sofa_team_stats; DELETE FROM sofa_events_cache; DELETE FROM odds_cache;")
            conn.commit()
        finally:
            conn.close()
    return jsonify({"status": "ok", "message": "Cache svuotata."})

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)