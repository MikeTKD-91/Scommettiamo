from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, json, logging, time
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import wraps

# ── Logging ────────────────────────────────────────────────────────────────────
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

# ── Timing decorator ───────────────────────────────────────────────────────────
def timed(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        t0 = time.perf_counter()
        result = fn(*a, **kw)
        log.info(f"{fn.__name__} completato in {time.perf_counter()-t0:.2f}s")
        return result
    return wrapper

# ── Database ───────────────────────────────────────────────────────────────────
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

# ── Poisson + Dixon-Coles (matrice normalizzata) ───────────────────────────────
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

# ── Modelli statistici ─────────────────────────────────────────────────────────
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

    n   = min((hs.get("matches") or 0) + (as_.get("matches") or 0) if hs and as_ else 0, 60)
    w_g = min(n / 40, 0.70)
    lh  = lh_g * w_g + lh_xg * (1 - w_g)
    la  = la_g * w_g + la_xg * (1 - w_g)
    lh *= 0.80 + exp_form(hs) * 0.40
    la *= 0.80 + exp_form(as_) * 0.40

    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

# ── SofaScore fetc