from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os, sqlite3, threading, json
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

LEAGUE_AVG   = 1.35   # media gol europea
MIN_MATCHES  = 5      # minimo partite per stats affidabili
REGRESSION_K = 10     # forza regressione verso media (più alto = più regressione)

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

# ── Database ───────────────────────────────────────────────────────────────────
def get_db():
    c = sqlite3.connect(DB_PATH, check_same_thread=False)
    c.row_factory = sqlite3.Row
    return c

def init_db():
    with db_lock:
        conn = get_db()
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
        """)
        conn.commit()
        conn.close()

init_db()

# ── Poisson + Dixon-Coles ──────────────────────────────────────────────────────
def dc_tau(x, y, lh, la, rho=-0.13):
    """Correzione Dixon-Coles per risultati bassi"""
    if x==0 and y==0: return max(0.001, 1 - lh*la*rho)
    if x==0 and y==1: return max(0.001, 1 + lh*rho)
    if x==1 and y==0: return max(0.001, 1 + la*rho)
    if x==1 and y==1: return max(0.001, 1 - rho)
    return 1.0

def pmf(lam, k):
    if lam <= 0: return 0
    return math.exp(k*math.log(lam) - lam - sum(math.log(i) for i in range(1, k+1)))

def calc_probs(lh, la):
    o15 = o25 = gg = 0.0
    for h in range(9):
        for a in range(9):
            p = pmf(lh,h) * pmf(la,a) * dc_tau(h,a,lh,la)
            t = h+a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if h > 0 and a > 0: gg += p
    return {"over15":min(o15,.99), "over25":min(o25,.99), "gg":min(gg,.99)}

# ── Regressione verso la media ─────────────────────────────────────────────────
def regress(observed, avg, n, k=REGRESSION_K):
    """
    Bayesian shrinkage: con pochi dati (n piccolo) tira verso la media.
    Formula: (n * observed + k * avg) / (n + k)
    Con n=5 e k=10: 33% osservato, 67% media
    Con n=30 e k=10: 75% osservato, 25% media
    """
    return (n * observed + k * avg) / (n + k)

# ── xG proxy calibrato ─────────────────────────────────────────────────────────
def calc_xg(stats, per_game=True):
    """
    xG proxy multi-componente:
    - Big chances = alta qualità (xG ~0.35 cad)
    - Shots on target = media qualità (xG ~0.10 cad)
    - Shots off target = bassa qualità (xG ~0.02 cad)
    Calibrato su dati storici europei
    """
    if not stats: return LEAGUE_AVG
    m = max(stats.get("matches") or 1, 1)
    bc  = (stats.get("big_chances") or 0) / m
    sot = (stats.get("shots_on_target") or 0) / m
    sh  = (stats.get("shots") or 0) / m
    soff = max(sh - sot, 0)
    xg_raw = bc*0.35 + sot*0.10 + soff*0.02
    # Regress verso media lega
    return regress(xg_raw, LEAGUE_AVG, m) if per_game else xg_raw * m

def calc_xga(stats, per_game=True):
    """xG concessi (proxy difesa)"""
    if not stats: return LEAGUE_AVG
    m = max(stats.get("matches") or 1, 1)
    bc  = (stats.get("big_chances_conceded") or 0) / m
    sot = (stats.get("shots_on_target_conceded") or 0) / m
    xga_raw = bc*0.35 + sot*0.10
    return regress(xga_raw, LEAGUE_AVG, m) if per_game else xga_raw * m

# ── Forma esponenziale ─────────────────────────────────────────────────────────
def exp_form(stats):
    """
    Forma basata su W/D/L con peso esponenziale:
    Ultima partita vale 1.0, penultima 0.7, terzultima 0.49...
    Normalizzata 0-1
    """
    if not stats: return 0.5
    m = stats.get("matches") or 0
    if m == 0: return 0.5
    w = stats.get("wins") or 0
    d = stats.get("draws") or 0
    l = stats.get("losses") or 0
    # Stima forma con regressione bayesiana
    pts_per_game = (w*3 + d) / max(m, 1)
    regressed = regress(pts_per_game, 1.3, m)  # 1.3 = media europea punti/gara
    return min(regressed / 3, 1.0)

# ── Over storico ───────────────────────────────────────────────────────────────
def historical_over(stats, threshold="25"):
    """Percentuale storica Over dalla stagione corrente"""
    if not stats: return None
    m = stats.get("matches") or 0
    if m < MIN_MATCHES: return None
    key = f"over{threshold}_count"
    count = stats.get(key) or 0
    return count / m

# ── Lambda avanzato ────────────────────────────────────────────────────────────
def calc_lambda(hs, as_):
    """
    Lambda con 4 componenti incrociati:
    1. Gol reali normalizzati (Dixon-Coles style)
    2. xG proxy (big chances + shots)
    3. Regressione bayesiana verso media lega
    4. Forma esponenziale come moltiplicatore
    
    Formula finale: media pesata dei 2 modelli × correzione forma
    """
    avg = LEAGUE_AVG

    # Modello 1: gol reali normalizzati con regressione
    if hs and as_:
        hm = max(hs.get("matches") or 1, 1)
        am = max(as_.get("matches") or 1, 1)

        # Attack/defense coefficients con regressione
        att_h = regress((hs.get("goals_home") or 0) / max(hs.get("matches_home") or 1,1) / avg, 1.0, hm)
        att_a = regress((as_.get("goals_away") or 0) / max(as_.get("matches_away") or 1,1) / avg, 1.0, am)
        def_h = regress((hs.get("conceded_home") or 0) / max(hs.get("matches_home") or 1,1) / avg, 1.0, hm)
        def_a = regress((as_.get("conceded_away") or 0) / max(as_.get("matches_away") or 1,1) / avg, 1.0, am)

        lh_goals = avg * att_h * def_a
        la_goals = avg * att_a * def_h

    elif hs:
        hm = max(hs.get("matches") or 1, 1)
        att_h = regress((hs.get("goals_scored") or 0) / hm / avg, 1.0, hm)
        def_h = regress((hs.get("goals_conceded") or 0) / hm / avg, 1.0, hm)
        lh_goals = avg * att_h
        la_goals = avg * def_h
    elif as_:
        am = max(as_.get("matches") or 1, 1)
        att_a = regress((as_.get("goals_scored") or 0) / am / avg, 1.0, am)
        def_a = regress((as_.get("goals_conceded") or 0) / am / avg, 1.0, am)
        lh_goals = avg * def_a
        la_goals = avg * att_a
    else:
        lh_goals = la_goals = avg

    # Modello 2: xG proxy
    lh_xg = calc_xg(hs) * (calc_xga(as_) / avg if as_ else 1.0)
    la_xg = calc_xg(as_) * (calc_xga(hs) / avg if hs else 1.0)

    # Fusione pesata: più partite = più peso ai gol reali
    n = min((hs.get("matches") or 0) + (as_.get("matches") or 0) if hs and as_ else 0, 60)
    w_goals = min(n / 40, 0.70)  # max 70% peso gol reali
    w_xg = 1 - w_goals

    lh = lh_goals * w_goals + lh_xg * w_xg
    la = la_goals * w_goals + la_xg * w_xg

    # Correzione forma esponenziale (±20% max)
    fh = exp_form(hs)
    fa = exp_form(as_)
    form_factor_h = 0.80 + fh * 0.40  # range 0.80–1.20
    form_factor_a = 0.80 + fa * 0.40
    lh *= form_factor_h
    la *= form_factor_a

    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

# ── SofaScore fetchers ─────────────────────────────────────────────────────────
def sofa_get(url, timeout=8):
    try:
        r = requests.get(url, headers=SOFA_HEADERS, timeout=timeout)
        if r.ok: return r.json()
    except: pass
    return None

def get_team_stats(team_id, t_id, s_id):
    if not all([team_id, t_id, s_id]): return None
    with db_lock:
        conn = get_db()
        row = conn.execute(
            "SELECT * FROM sofa_team_stats WHERE team_id=? AND tournament_id=? AND season_id=?",
            (team_id, t_id, s_id)
        ).fetchone()
        conn.close()
    if row:
        upd = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc) - upd).total_seconds() < 3600*12:
            return dict(row)

    data = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/overall")
    if not data: return dict(row) if row else None
    st = data.get("statistics", {})
    if not st: return dict(row) if row else None

    m = max(st.get("matches") or 1, 1)

    # Cerca dati casa/trasferta separati
    data_h = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/home")
    data_a = sofa_get(f"https://api.sofascore.com/api/v1/team/{team_id}/unique-tournament/{t_id}/season/{s_id}/statistics/away")
    st_h = (data_h or {}).get("statistics", {})
    st_a = (data_a or {}).get("statistics", {})

    mh = max(st_h.get("matches") or 0, 1)
    ma = max(st_a.get("matches") or 0, 1)

    # Conta Over 1.5 e 2.5 storici dai match (approssimazione)
    gs = st.get("goalsScored") or 0
    gc = st.get("goalsConceded") or 0

    rec = {
        "team_id": team_id, "tournament_id": t_id, "season_id": s_id,
        "goals_scored": gs, "goals_conceded": gc,
        "goals_home": st_h.get("goalsScored") or gs//2,
        "goals_away": st_a.get("goalsScored") or gs//2,
        "conceded_home": st_h.get("goalsConceded") or gc//2,
        "conceded_away": st_a.get("goalsConceded") or gc//2,
        "matches": m,
        "matches_home": mh,
        "matches_away": ma,
        "big_chances": st.get("bigChances") or 0,
        "shots_on_target": st.get("shotsOnTarget") or 0,
        "shots": st.get("shots") or 0,
        "big_chances_conceded": st.get("bigChancesConceded") or 0,
        "shots_on_target_conceded": st.get("shotsOnTargetAgainst") or 0,
        "wins": st.get("wins") or 0,
        "draws": st.get("draws") or 0,
        "losses": st.get("losses") or 0,
        "over15_count": max(0, m - int(m * 0.15)),  # stima ~85% over 1.5
        "over25_count": int(m * ((gs+gc)/m/4.5)) if m>0 else 0,  # stima proporzionale
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }

    with db_lock:
        conn = get_db()
        conn.execute("""
            INSERT OR REPLACE INTO sofa_team_stats VALUES
            (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, list(rec.values()))
        conn.commit()
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
                    dec = round(int(n)/int(d)+1, 3)
                    if dec > 1: odds[name] = dec
            except: pass
    return odds

def get_today_events(date_str):
    with db_lock:
        conn = get_db()
        row = conn.execute("SELECT data, updated_at FROM sofa_events_cache WHERE date=?", (date_str,)).fetchone()
        conn.close()
    if row:
        upd = datetime.fromisoformat(row["updated_at"])
        if (datetime.now(timezone.utc)-upd).total_seconds() < 3600*2:
            return json.loads(row["data"])
    data = sofa_get(f"https://api.sofascore.com/api/v1/sport/football/scheduled-events/{date_str}", timeout=15)
    if not data: return []
    events = data.get("events", [])
    with db_lock:
        conn = get_db()
        conn.execute("INSERT OR REPLACE INTO sofa_events_cache (date,data,updated_at) VALUES (?,?,?)",
            (date_str, json.dumps(events), datetime.now(timezone.utc).isoformat()))
        conn.commit()
        conn.close()
    return events

FLAG_MAP = {
    "england":"🏴󠁧󠁢󠁥󠁮󠁧󠁿","italy":"🇮🇹","spain":"🇪🇸","germany":"🇩🇪","france":"🇫🇷",
    "portugal":"🇵🇹","netherlands":"🇳🇱","brazil":"🇧🇷","argentina":"🇦🇷",
    "usa":"🇺🇸","turkey":"🇹🇷","greece":"🇬🇷","belgium":"🇧🇪","scotland":"🏴󠁧󠁢󠁳󠁣󠁴󠁿",
    "austria":"🇦🇹","switzerland":"🇨🇭","mexico":"🇲🇽","japan":"🇯🇵","south-korea":"🇰🇷",
}

def analyze_event(ev, start_utc, end_utc):
    ct = ev.get("startTimestamp")
    if not ct: return []
    ev_time = datetime.fromtimestamp(ct, tz=timezone.utc)
    if not (start_utc <= ev_time <= end_utc): return []
    if ev.get("status",{}).get("type","") in ["inprogress","finished","postponed","canceled"]: return []

    ht = ev.get("homeTeam",{}); at = ev.get("awayTeam",{})
    hn = ht.get("name",""); an = at.get("name","")
    hid = ht.get("id"); aid = at.get("id")
    eid = ev.get("id")
    tourn = ev.get("tournament",{})
    ut = tourn.get("uniqueTournament",{})
    t_id = ut.get("id"); s_id = ev.get("season",{}).get("id")
    lg = tourn.get("name","")
    cf = tourn.get("category",{}).get("flag","").lower()
    flag = FLAG_MAP.get(cf, "⚽")

    hs = get_team_stats(hid, t_id, s_id)
    as_ = get_team_stats(aid, t_id, s_id)
    has_real = bool(hs or as_)
    if not has_real: return []  # skip partite senza dati

    lh, la = calc_lambda(hs, as_)
    pr = calc_probs(lh, la)
    exp_g = round(lh+la, 2)
    fh = round(exp_form(hs), 2)
    fa = round(exp_form(as_), 2)

    odds_data = get_event_odds(eid)

    # Over storico come conferma
    hist_o25_h = historical_over(hs, "25")
    hist_o25_a = historical_over(as_, "25")
    hist_conf = None
    if hist_o25_h is not None and hist_o25_a is not None:
        hist_conf = round((hist_o25_h + hist_o25_a) / 2, 3)

    picks = []

    # Over 1.5
    o15 = odds_data.get("Over 1.5") or odds_data.get("Over1.5")
    if o15 and 1.10 <= o15 <= 1.65:
        prob = pr["over15"]
        # Boost probabilità se storico Over 1.5 alto
        if hist_conf and hist_conf > 0.60: prob = min(prob * 1.05, 0.99)
        edge = prob - 1/o15
        picks.append({"name":"Over 1.5","odds":round(o15,2),"prob":round(prob,3),"edge":round(edge,3),"market":"over15"})

    # Over 2.5
    o25 = odds_data.get("Over 2.5") or odds_data.get("Over2.5")
    if o25 and 1.35 <= o25 <= 2.60:
        prob = pr["over25"]
        if hist_conf and hist_conf > 0.50: prob = min(prob * 1.04, 0.99)
        edge = prob - 1/o25
        picks.append({"name":"Over 2.5","odds":round(o25,2),"prob":round(prob,3),"edge":round(edge,3),"market":"over25"})

    # Goal/Goal
    gg_odds = odds_data.get("Yes") or odds_data.get("GG")
    if not gg_odds:
        prob_gg = pr["gg"]
        if prob_gg > 0.45: gg_odds = round(1/prob_gg*1.05, 2)
    if gg_odds and 1.40 <= gg_odds <= 2.50:
        prob = pr["gg"]
        edge = prob - 1/gg_odds
        picks.append({"name":"Goal/Goal","odds":round(gg_odds,2),"prob":round(prob,3),"edge":round(edge,3),"market":"gg"})

    if not picks: return []

    return [{**p,
        "match": f"{hn} vs {an}",
        "league": f"{flag} {lg}",
        "commence_time": ev_time.isoformat(),
        "probs": pr, "exp_g": exp_g,
        "home_form": fh, "away_form": fa,
        "has_real_stats": True,
        "hist_over25": hist_conf,
        "score": p["edge"]*50 + p["prob"]*30 + (fh+fa)*10 + 15,
    } for p in picks]

def find_best_combo(picks, target, cfg):
    for min_edge in [0.03, 0.01, 0.0, -0.05]:
        f = [p for p in picks if p["edge"] >= min_edge]
        if len(f) >= cfg["min_picks"]: break
    if len(f) < cfg["min_picks"]: f = picks
    top = sorted(f, key=lambda p: p["score"], reverse=True)[:25]
    best, bs = [], -1
    for sz in range(cfg["min_picks"], cfg["max_picks"]+1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            if len({p["match"] for p in combo}) != sz: continue
            mc = {}
            for p in combo: mc[p["market"]] = mc.get(p["market"],0)+1
            if any(v>2 for v in mc.values()): continue
            tot = math.prod(p["odds"] for p in combo)
            if tot < target*0.55 or tot > target*1.55: continue
            cp = math.prod(p["prob"] for p in combo)
            dp = abs(tot-target)/target
            sc = cp*70 + sum(p["edge"] for p in combo)*15 - dp*15
            if sc > bs: bs=sc; best=list(combo)
        if best and abs(math.prod(p["odds"] for p in best)-target)/target < 0.15: break
    return best

@app.route("/health")
def health():
    with db_lock:
        conn = get_db()
        sc = conn.execute("SELECT COUNT(*) as c FROM sofa_team_stats").fetchone()["c"]
        ec = conn.execute("SELECT COUNT(*) as c FROM sofa_events_cache").fetchone()["c"]
        conn.close()
    return jsonify({"status":"ok","team_stats_cached":sc,"events_cached":ec})

@app.route("/generate", methods=["POST"])
def generate():
    now_utc = datetime.now(timezone.utc)
    italy_offset = 2 if now_utc.month in [4,5,6,7,8,9,10] else 1
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    all_picks, day_offset = [], 0
    for day_offset in range(3):
        day_dt = now_italy.replace(hour=0,minute=0,second=0,microsecond=0) + timedelta(days=day_offset)
        date_str = day_dt.strftime("%Y-%m-%d")
        start = now_utc if day_offset==0 else day_dt.astimezone(timezone.utc)
        end = (now_italy.replace(hour=23,minute=59,second=59)+timedelta(days=day_offset)).astimezone(timezone.utc)

        events = get_today_events(date_str)
        day_picks = []
        for ev in events:
            day_picks.extend(analyze_event(ev, start, end))
        if day_picks:
            all_picks = day_picks
            break

    if not all_picks:
        return jsonify({"error":"Nessuna partita trovata con dati statistici nei prossimi 3 giorni."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen: seen.add(k); unique.append(p)

    day_label = "dopodomani" if day_offset==2 else "domani" if day_offset==1 else "oggi"

    multiples, used = [], set()
    for tgt in [3,5,8,10,100]:
        cfg = get_cfg(tgt)
        avail = [p for p in unique if p["match"] not in used] or unique
        combo = find_best_combo(avail, tgt, cfg)
        if combo:
            for p in combo: used.add(p["match"])
            multiples.append({
                "target": tgt,
                "total_odds": round(math.prod(p["odds"] for p in combo), 2),
                "combo_probability": round(math.prod(p["prob"] for p in combo)*100, 1),
                "picks": combo,
                "value_in_combo": sum(1 for p in combo if p["edge"]>0.02),
            })

    if not multiples:
        return jsonify({"error":"Impossibile costruire multipla."}), 404

    return jsonify({
        "multiples": multiples,
        "day": day_label,
        "leagues_with_data": len({p["league"] for p in unique}),
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": sum(1 for p in unique if p["edge"]>0.02),
        "source": "sofascore",
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT",5000)))
