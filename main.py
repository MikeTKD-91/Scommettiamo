from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os
from datetime import datetime, timezone, timedelta

app = Flask(__name__)
CORS(app)

LEAGUES = [
    # Top 5 europei — weekend + coppe
    {"key": "soccer_epl",                        "name": "Premier League",    "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": "PL"},
    {"key": "soccer_italy_serie_a",              "name": "Serie A",           "flag": "🇮🇹",  "fd_code": "SA"},
    {"key": "soccer_spain_la_liga",              "name": "La Liga",           "flag": "🇪🇸",  "fd_code": "PD"},
    {"key": "soccer_germany_bundesliga",         "name": "Bundesliga",        "flag": "🇩🇪",  "fd_code": "BL1"},
    {"key": "soccer_france_ligue_one",           "name": "Ligue 1",           "flag": "🇫🇷",  "fd_code": "FL1"},
    # Coppe europee — martedi/giovedi
    {"key": "soccer_uefa_champs_league",         "name": "Champions League",  "flag": "🏆",   "fd_code": "CL"},
    {"key": "soccer_uefa_europa_league",         "name": "Europa League",     "flag": "🏆",   "fd_code": "EL"},
    {"key": "soccer_uefa_europa_conference_league", "name": "Conference League", "flag": "🏆", "fd_code": None},
    # Qualificazioni mondiali — infrasettimanale
    {"key": "soccer_fifa_world_cup_qualifiers_europe", "name": "Qual. Mondiali", "flag": "🌍", "fd_code": None},
    # Seconde divisioni europee — infrasettimanale
    {"key": "soccer_efl_champ",                  "name": "Championship",      "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_italy_serie_b",              "name": "Serie B",           "flag": "🇮🇹",  "fd_code": None},
    {"key": "soccer_spain_segunda_division",     "name": "La Liga 2",         "flag": "🇪🇸",  "fd_code": None},
    {"key": "soccer_germany_bundesliga2",        "name": "Bundesliga 2",      "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_england_league1",            "name": "League One",        "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_germany_liga3",              "name": "3. Liga",           "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_france_ligue_two",           "name": "Ligue 2",           "flag": "🇫🇷",  "fd_code": None},
    # Altri europei con partite infrasettimanali
    {"key": "soccer_portugal_primeira_liga",     "name": "Primeira Liga",     "flag": "🇵🇹",  "fd_code": "PPL"},
    {"key": "soccer_netherlands_eredivisie",     "name": "Eredivisie",        "flag": "🇳🇱",  "fd_code": "DED"},
    {"key": "soccer_belgium_first_div",          "name": "Jupiler Pro League","flag": "🇧🇪",  "fd_code": None},
    {"key": "soccer_greece_super_league",        "name": "Super League",      "flag": "🇬🇷",  "fd_code": None},
    {"key": "soccer_turkey_super_lig",           "name": "Süper Lig",         "flag": "🇹🇷",  "fd_code": None},
    {"key": "soccer_austria_bundesliga",         "name": "Bundesliga AT",     "flag": "🇦🇹",  "fd_code": None},
    {"key": "soccer_switzerland_superleague",    "name": "Super League CH",   "flag": "🇨🇭",  "fd_code": None},
    {"key": "soccer_spl",                        "name": "Scottish Premier",  "flag": "🏴󠁧󠁢󠁳󠁣󠁴󠁿", "fd_code": None},
    # Sudamerica — giocano spesso infrasettimanale
    {"key": "soccer_brazil_campeonato",          "name": "Brasil Série A",    "flag": "🇧🇷",  "fd_code": None},
    {"key": "soccer_argentina_primera_division", "name": "Primera División",  "flag": "🇦🇷",  "fd_code": None},
    {"key": "soccer_conmebol_copa_libertadores", "name": "Copa Libertadores", "flag": "🌎",   "fd_code": None},
    # USA/Asia — coprono i giorni vuoti
    {"key": "soccer_usa_mls",                    "name": "MLS",               "flag": "🇺🇸",  "fd_code": None},
    {"key": "soccer_japan_j_league",             "name": "J-League",          "flag": "🇯🇵",  "fd_code": None},
    {"key": "soccer_korea_kleague1",             "name": "K League 1",        "flag": "🇰🇷",  "fd_code": None},
    {"key": "soccer_mexico_ligamx",              "name": "Liga MX",           "flag": "🇲🇽",  "fd_code": None},
]

TARGET_CONFIG = {
    3:   {"min_picks": 2, "max_picks": 3, "min_odds": 1.15, "max_odds": 2.10},
    5:   {"min_picks": 3, "max_picks": 4, "min_odds": 1.15, "max_odds": 2.20},
    8:   {"min_picks": 4, "max_picks": 5, "min_odds": 1.15, "max_odds": 2.40},
    10:  {"min_picks": 4, "max_picks": 6, "min_odds": 1.15, "max_odds": 2.50},
    100: {"min_picks": 6, "max_picks": 9, "min_odds": 1.15, "max_odds": 3.50},
}

LEAGUE_AVG = 1.35  # media europea gol per squadra per partita
_stats_cache = {}
_team_id_cache = {}

def get_cfg(target):
    for k in sorted(TARGET_CONFIG.keys()):
        if target <= k: return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

# ── Dixon-Coles correction ─────────────────────────────────────────────────────
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

# ── Forma pesata (recente conta di piu) ───────────────────────────────────────
def weighted_form(matches_data, is_home):
    """Peso decrescente: partita piu recente = peso 5, piu vecchia = peso 1"""
    n = len(matches_data)
    if n == 0: return 0.5
    total_w = total_pts = 0
    for i, m in enumerate(matches_data):
        w = n - i  # peso: prima partita = peso n, ultima = peso 1
        total_w += w
        r = m["result_home"] if is_home else m["result_away"]
        pts = 3 if r == "W" else 1 if r == "D" else 0
        total_pts += pts * w
    return total_pts / (total_w * 3)

# ── football-data.org ─────────────────────────────────────────────────────────
def load_team_ids(fd_code, fd_key):
    if fd_code in _team_id_cache: return _team_id_cache[fd_code]
    try:
        r = requests.get(f"https://api.football-data.org/v4/competitions/{fd_code}/teams",
            headers={"X-Auth-Token": fd_key}, timeout=8)
        if not r.ok: return {}
        mapping = {}
        for t in r.json().get("teams", []):
            mapping[t["name"].lower()] = t["id"]
            mapping[t["shortName"].lower()] = t["id"]
            if t.get("tla"): mapping[t["tla"].lower()] = t["id"]
        _team_id_cache[fd_code] = mapping
        return mapping
    except: return {}

def find_team_id(name, fd_code, fd_key):
    mapping = load_team_ids(fd_code, fd_key)
    nl = name.lower()
    if nl in mapping: return mapping[nl]
    for k, v in mapping.items():
        if nl in k or k in nl: return v
    return None

def get_stats(name, fd_code, fd_key):
    if not fd_code: return None
    ck = f"{name}_{fd_code}"
    if ck in _stats_cache: return _stats_cache[ck]
    try:
        tid = find_team_id(name, fd_code, fd_key)
        if not tid: return None
        r = requests.get(
            f"https://api.football-data.org/v4/teams/{tid}/matches?status=FINISHED&limit=10",
            headers={"X-Auth-Token": fd_key}, timeout=8)
        if not r.ok: return None
        matches = r.json().get("matches", [])
        if not matches: return None

        home_matches = []
        away_matches = []
        gfh = gfa = gah = gaa = ph = pa = 0

        for m in matches:
            hn = m["homeTeam"]["name"]
            sc = m["score"]["fullTime"]
            gh = sc.get("home", 0) or 0
            ga = sc.get("away", 0) or 0
            is_home = name.lower() in hn.lower() or hn.lower() in name.lower()

            if is_home:
                gfh += gh; gah += ga; ph += 1
                res = "W" if gh > ga else "D" if gh == ga else "L"
                home_matches.append({"result_home": res, "gf": gh, "ga": ga})
            else:
                gfa += ga; gaa += gh; pa += 1
                res = "W" if ga > gh else "D" if ga == gh else "L"
                away_matches.append({"result_away": res, "gf": ga, "ga": gh})

        # Coefficienti attacco/difesa normalizzati sulla media lega
        att_h = (gfh/ph / LEAGUE_AVG) if ph > 0 else 1.0
        att_a = (gfa/pa / LEAGUE_AVG) if pa > 0 else 1.0
        def_h = (gah/ph / LEAGUE_AVG) if ph > 0 else 1.0
        def_a = (gaa/pa / LEAGUE_AVG) if pa > 0 else 1.0

        # Forma pesata
        wf_home = weighted_form(home_matches, True)
        wf_away = weighted_form(away_matches, False)

        # Fattore casa specifico squadra
        # Se segna molto di piu in casa che in trasferta = alto vantaggio casalingo
        home_advantage = (gfh/ph) / (gfa/pa) if ph > 0 and pa > 0 and gfa > 0 else 1.15

        res = {
            "att_h": att_h, "att_a": att_a,
            "def_h": def_h, "def_a": def_a,
            "wf_home": wf_home, "wf_away": wf_away,
            "home_advantage": min(home_advantage, 2.0),
            "avg_gf_h": gfh/ph if ph > 0 else LEAGUE_AVG,
            "avg_gf_a": gfa/pa if pa > 0 else LEAGUE_AVG,
            "avg_ga_h": gah/ph if ph > 0 else LEAGUE_AVG,
            "avg_ga_a": gaa/pa if pa > 0 else LEAGUE_AVG,
            "games_in_7days": 0,  # placeholder
        }
        _stats_cache[ck] = res
        return res
    except: return None

def calc_lambda(hs, as_):
    """
    Calcola gol attesi con incroci avanzati:
    1. Coefficienti attacco/difesa normalizzati
    2. Media lega come riferimento
    3. Fattore casa pesato
    4. Correzione forma recente
    """
    avg = LEAGUE_AVG

    if hs and as_:
        # Lambda casa = media lega * attacco casa * difesa trasferta avversaria
        lh = avg * hs["att_h"] * as_["def_a"]
        # Lambda trasferta = media lega * attacco trasferta * difesa casa avversaria
        la = avg * as_["att_a"] * hs["def_h"]

        # Correggi con fattore casa specifico
        lh *= min(hs["home_advantage"], 1.4)

        # Correggi con forma recente (±15% max)
        form_factor_h = 0.85 + (hs["wf_home"] * 0.30)  # range 0.85-1.15
        form_factor_a = 0.85 + (as_["wf_away"] * 0.30)
        lh *= form_factor_h
        la *= form_factor_a

    elif hs:
        lh = avg * hs["att_h"]
        la = avg * hs["def_h"]
        lh *= min(hs["home_advantage"], 1.3)
        lh *= 0.85 + hs["wf_home"] * 0.30
    elif as_:
        lh = avg * as_["def_a"]
        la = avg * as_["att_a"]
        la *= 0.85 + as_["wf_away"] * 0.30
    else:
        lh = la = avg

    return max(0.3, min(4.5, lh)), max(0.3, min(4.5, la))

def analyze_event(event, league, fd_key):
    home, away = event["home_team"], event["away_team"]
    fd_code = league.get("fd_code")
    hs  = get_stats(home, fd_code, fd_key) if fd_key and fd_code else None
    as_ = get_stats(away, fd_code, fd_key) if fd_key and fd_code else None

    lh, la = calc_lambda(hs, as_)
    pr = calc_probs(lh, la)
    exp_g = round(lh + la, 2)
    has_real = bool(hs or as_)

    # Forma display
    hf = hs["wf_home"] if hs else 0.5
    af = as_["wf_away"] if as_ else 0.5

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
                    picks.append({"name": "Over 1.5", "odds": round(odds,2),
                        "prob": round(prob,3), "edge": round(edge,3),
                        "market": "over15", "probs": pr, "exp_g": exp_g,
                        "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                        "lh": round(lh,2), "la": round(la,2)})

            if point == 2.5 and name_o == "Over":
                prob = pr["over25"]
                edge = prob - 1/odds
                if 1.35 <= odds <= 2.60:
                    picks.append({"name": "Over 2.5", "odds": round(odds,2),
                        "prob": round(prob,3), "edge": round(edge,3),
                        "market": "over25", "probs": pr, "exp_g": exp_g,
                        "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                        "lh": round(lh,2), "la": round(la,2)})

            # GG stimato da Over 2.5 se btts non disponibile
            if point == 2.5 and name_o == "Over":
                prob_gg = pr["gg"]
                # Stima quota GG dal bookmaker Over2.5
                est_gg_odds = round(1 / prob_gg * 1.05, 2) if prob_gg > 0 else 0
                if 1.40 <= est_gg_odds <= 2.50 and prob_gg > 0.45:
                    edge_gg = prob_gg - 1/est_gg_odds
                    picks.append({"name": "Goal/Goal", "odds": est_gg_odds,
                        "prob": round(prob_gg,3), "edge": round(edge_gg,3),
                        "market": "gg", "probs": pr, "exp_g": exp_g,
                        "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                        "lh": round(lh,2), "la": round(la,2)})
        break

    return [{
        **p,
        "match": f"{home} vs {away}",
        "league": f"{league['flag']} {league['name']}",
        "commence_time": event.get("commence_time"),
        "score": p["edge"]*50 + p["prob"]*30 + (hf+af)*10 + (10 if has_real else 0),
    } for p in picks]

def find_best_combo(all_picks, target, cfg):
    for min_edge in [0.03, 0.01, 0.0, -0.05]:
        filtered = [p for p in all_picks
            if p["edge"] >= min_edge
            and cfg["min_odds"] <= p["odds"] <= cfg["max_odds"]]
        if len(filtered) >= cfg["min_picks"]: break

    if len(filtered) < cfg["min_picks"]:
        filtered = all_picks

    top = sorted(filtered, key=lambda p: p["score"], reverse=True)[:30]
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
            diff_pen   = abs(tot - target) / target
            score = combo_prob * 70 + sum(p["edge"] for p in combo) * 15 - diff_pen * 15

            if score > best_score:
                best_score = score
                best = list(combo)

        if best and abs(math.prod(p["odds"] for p in best) - target) / target < 0.15:
            break

    return best

@app.route("/health")
def health():
    return jsonify({"status": "ok"})

@app.route("/generate", methods=["POST"])
def generate():
    body     = request.get_json() or {}
    odds_key = (body.get("odds_api_key") or "").strip()
    fd_key   = (body.get("football_api_key") or "").strip() or None

    if not odds_key:
        return jsonify({"error": "Odds API key mancante"}), 400

    now_utc = datetime.now(timezone.utc)
    italy_offset = 2 if now_utc.month in [4,5,6,7,8,9,10] else 1
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)

    def fetch_picks(start_utc, end_utc):
        picks, found = [], []
        for lg in LEAGUES:
            try:
                url = (f"https://api.the-odds-api.com/v4/sports/{lg['key']}/odds/"
                       f"?apiKey={odds_key}&regions=eu&markets=totals&oddsFormat=decimal")
                r = requests.get(url, timeout=8)
                if not r.ok: continue
                events = r.json()
                if not isinstance(events, list) or not events: continue
                day_events = []
                for ev in events:
                    ct = ev.get("commence_time", "")
                    if not ct: continue
                    try:
                        t = datetime.fromisoformat(ct.replace("Z", "+00:00"))
                        if start_utc <= t <= end_utc:
                            day_events.append(ev)
                    except: continue
                if not day_events: continue
                found.append(lg["name"])
                for ev in day_events:
                    picks.extend(analyze_event(ev, lg, fd_key))
            except: continue
            if len(picks) >= 150: break
        return picks, found

    # Cerca oggi, domani, dopodomani — una sola sessione di chiamate API
    all_picks, leagues_found, is_tomorrow, day_offset = [], [], False, 0
    for day_offset in range(3):
        start = (now_italy.replace(hour=0, minute=0, second=0, microsecond=0) + timedelta(days=day_offset)).astimezone(timezone.utc)
        end   = (now_italy.replace(hour=23, minute=59, second=59) + timedelta(days=day_offset)).astimezone(timezone.utc)
        if day_offset == 0:
            start = now_utc
        all_picks, leagues_found = fetch_picks(start, end)
        if all_picks:
            is_tomorrow = day_offset > 0
            break

    if not all_picks:
        return jsonify({"error": "Nessuna partita trovata nei prossimi 3 giorni. Riprova più tardi."}), 404

    # Deduplica
    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    day_label = "dopodomani" if day_offset == 2 else "domani" if day_offset == 1 else "oggi"

    # Genera una multipla per ogni target — pick NON ripetuti tra multipla
    TARGETS = [3, 5, 8, 10]
    multiples = []
    used_matches = set()  # traccia partite gia usate

    for target in TARGETS:
        cfg = get_cfg(target)

        # Escludi pick di partite gia usate nelle multipla precedenti
        available = [p for p in unique if p["match"] not in used_matches]
        if not available:
            available = unique  # fallback: riusa tutto se non bastano

        combo = find_best_combo(available, target, cfg)
        if combo:
            # Aggiungi le partite usate al set
            for p in combo:
                used_matches.add(p["match"])

            total_odds  = round(math.prod(p["odds"] for p in combo), 2)
            combo_prob  = round(math.prod(p["prob"] for p in combo) * 100, 1)
            value_count = sum(1 for p in combo if p["edge"] > 0.02)

            multiples.append({
                "target":            target,
                "total_odds":        total_odds,
                "combo_probability": combo_prob,
                "picks":             combo,
                "value_in_combo":    value_count,
            })

    if not multiples:
        return jsonify({"error": "Impossibile costruire multipla. Riprova tra qualche ora."}), 404

    return jsonify({
        "multiples":         multiples,
        "day":               day_label,
        "leagues_with_data": len(leagues_found),
        "matches_analyzed":  len({p["match"] for p in unique}),
        "value_bets_found":  sum(1 for p in unique if p["edge"] > 0.02),
        "football_api_used": fd_key is not None,
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
