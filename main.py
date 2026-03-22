from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os
from datetime import datetime, timezone, timedelta

app = Flask(__name__)
CORS(app)

LEAGUES = [
    {"key": "soccer_epl",                    "name": "Premier League",   "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": "PL"},
    {"key": "soccer_italy_serie_a",          "name": "Serie A",          "flag": "🇮🇹",  "fd_code": "SA"},
    {"key": "soccer_spain_la_liga",          "name": "La Liga",          "flag": "🇪🇸",  "fd_code": "PD"},
    {"key": "soccer_germany_bundesliga",     "name": "Bundesliga",       "flag": "🇩🇪",  "fd_code": "BL1"},
    {"key": "soccer_france_ligue_one",       "name": "Ligue 1",          "flag": "🇫🇷",  "fd_code": "FL1"},
    {"key": "soccer_efl_champ",              "name": "Championship",     "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_italy_serie_b",          "name": "Serie B",          "flag": "🇮🇹",  "fd_code": None},
    {"key": "soccer_spain_segunda_division", "name": "La Liga 2",        "flag": "🇪🇸",  "fd_code": None},
    {"key": "soccer_germany_bundesliga2",    "name": "Bundesliga 2",     "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_uefa_champs_league",     "name": "Champions League", "flag": "🏆",   "fd_code": "CL"},
    {"key": "soccer_england_league1",        "name": "League One",       "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fd_code": None},
    {"key": "soccer_germany_liga3",          "name": "3. Liga",          "flag": "🇩🇪",  "fd_code": None},
    {"key": "soccer_portugal_primeira_liga", "name": "Primeira Liga",    "flag": "🇵🇹",  "fd_code": "PPL"},
    {"key": "soccer_netherlands_eredivisie", "name": "Eredivisie",       "flag": "🇳🇱",  "fd_code": "DED"},
    {"key": "soccer_uefa_europa_league",     "name": "Europa League",    "flag": "🏆",   "fd_code": "EL"},
]

# Per ogni target: quanti Over1.5, Over2.5, GG usare
TARGET_CONFIG = {
    3:   {"min_picks": 2, "max_picks": 3, "min_odds": 1.15, "max_odds": 2.10},
    5:   {"min_picks": 3, "max_picks": 4, "min_odds": 1.15, "max_odds": 2.20},
    8:   {"min_picks": 4, "max_picks": 5, "min_odds": 1.15, "max_odds": 2.40},
    10:  {"min_picks": 4, "max_picks": 6, "min_odds": 1.15, "max_odds": 2.50},
    100: {"min_picks": 6, "max_picks": 9, "min_odds": 1.15, "max_odds": 3.50},
}

def get_cfg(target):
    for k in sorted(TARGET_CONFIG.keys()):
        if target <= k: return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

_stats_cache = {}
_team_id_cache = {}

def pmf(lam, k):
    if lam <= 0: return 0
    return math.exp(k * math.log(lam) - lam - sum(math.log(i) for i in range(1, k+1)))

def poisson_probs(lh, la):
    o15 = o25 = gg = 0.0
    for h in range(9):
        for a in range(9):
            p = pmf(lh, h) * pmf(la, a)
            t = h + a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if h > 0 and a > 0: gg += p
    return {
        "over15": min(o15, .99),
        "over25": min(o25, .99),
        "gg":     min(gg,  .99),
    }

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
        r = requests.get(f"https://api.football-data.org/v4/teams/{tid}/matches?status=FINISHED&limit=10",
            headers={"X-Auth-Token": fd_key}, timeout=8)
        if not r.ok: return None
        matches = r.json().get("matches", [])
        if not matches: return None
        gfh = gfa = gah = gaa = ph = pa = 0
        form = ""
        for m in matches:
            hn = m["homeTeam"]["name"]
            sc = m["score"]["fullTime"]
            gh = sc.get("home", 0) or 0
            ga = sc.get("away", 0) or 0
            is_home = name.lower() in hn.lower() or hn.lower() in name.lower()
            if is_home:
                gfh += gh; gah += ga; ph += 1
                form += "W" if gh > ga else "D" if gh == ga else "L"
            else:
                gfa += ga; gaa += gh; pa += 1
                form += "W" if ga > gh else "D" if ga == gh else "L"
        res = {
            "avg_for_h":     gfh/ph if ph > 0 else 1.35,
            "avg_for_a":     gfa/pa if pa > 0 else 1.35,
            "avg_against_h": gah/ph if ph > 0 else 1.35,
            "avg_against_a": gaa/pa if pa > 0 else 1.35,
            "form": form[-10:],
        }
        _stats_cache[ck] = res
        return res
    except: return None

def form_score(form):
    if not form: return 0.5
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in form[-5:]) / 15

def analyze_event(event, league, fd_key):
    home, away = event["home_team"], event["away_team"]
    avg = 1.35
    fd_code = league.get("fd_code")
    hs  = get_stats(home, fd_code, fd_key) if fd_key and fd_code else None
    as_ = get_stats(away, fd_code, fd_key) if fd_key and fd_code else None

    lh = hs["avg_for_h"] * (as_["avg_against_a"]/avg if as_ else 1) if hs else avg
    la = as_["avg_for_a"] * (hs["avg_against_h"]/avg if hs else 1) if as_ else avg
    lh = max(0.3, min(4.0, lh))
    la = max(0.3, min(4.0, la))

    pr  = poisson_probs(lh, la)
    hf  = form_score(hs["form"] if hs else "")
    af  = form_score(as_["form"] if as_ else "")
    exp_g = round(lh + la, 2)
    has_real = bool(hs or as_)

    picks = []

    for bk in event.get("bookmakers", []):
        markets = {m["key"]: m for m in bk.get("markets", [])}
        if "totals" not in markets: continue

        for o in markets["totals"]["outcomes"]:
            point = float(o.get("point", 0))
            odds  = float(o["price"])
            name_o = o["name"]  # "Over" or "Under"

            # Over 1.5
            if point == 1.5 and name_o == "Over":
                prob = pr["over15"]
                edge = prob - 1/odds
                if 1.10 <= odds <= 1.60:
                    picks.append({
                        "name": "Over 1.5", "odds": round(odds,2),
                        "prob": round(prob,3), "edge": round(edge,3),
                        "market": "over15", "probs": pr, "exp_g": exp_g,
                        "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                    })

            # Over 2.5
            if point == 2.5 and name_o == "Over":
                prob = pr["over25"]
                edge = prob - 1/odds
                if 1.40 <= odds <= 2.50:
                    picks.append({
                        "name": "Over 2.5", "odds": round(odds,2),
                        "prob": round(prob,3), "edge": round(edge,3),
                        "market": "over25", "probs": pr, "exp_g": exp_g,
                        "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                    })
        break  # un solo bookmaker

    # Goal/Goal — serve mercato btts, se non c'è lo stimiamo da Poisson
    gg_from_market = False
    for bk in event.get("bookmakers", []):
        for mkt in bk.get("markets", []):
            if mkt["key"] == "btts":
                for o in mkt["outcomes"]:
                    if o["name"] in ("Yes", "Si", "GG"):
                        odds = float(o["price"])
                        prob = pr["gg"]
                        edge = prob - 1/odds
                        if 1.40 <= odds <= 2.50:
                            picks.append({
                                "name": "Goal/Goal", "odds": round(odds,2),
                                "prob": round(prob,3), "edge": round(edge,3),
                                "market": "gg", "probs": pr, "exp_g": exp_g,
                                "home_form": round(hf,2), "away_form": round(af,2),
                                "has_real_stats": has_real,
                            })
                        gg_from_market = True
                break
        if gg_from_market: break

    return [{
        **p,
        "match": f"{home} vs {away}",
        "league": f"{league['flag']} {league['name']}",
        "commence_time": event.get("commence_time"),
        "score": p["edge"]*50 + p["prob"]*30 + (hf+af)*10 + (8 if has_real else 0),
    } for p in picks]

def find_best_combo(all_picks, target, cfg):
    """
    Logica progressiva:
    1. Prima cerca solo VALUE BET (edge > 0)
    2. Se non bastano, accetta tutto
    Privilegia sempre: alta prob combinata + quota vicina al target
    """
    for min_edge in [0.03, 0.01, 0.0, -0.05]:
        filtered = [p for p in all_picks
            if p["edge"] >= min_edge
            and cfg["min_odds"] <= p["odds"] <= cfg["max_odds"]]
        if len(filtered) >= cfg["min_picks"]:
            break

    if len(filtered) < cfg["min_picks"]:
        filtered = all_picks

    top = sorted(filtered, key=lambda p: p["score"], reverse=True)[:30]
    best, best_score = [], -1

    for sz in range(cfg["min_picks"], cfg["max_picks"]+1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            # No partite duplicate
            if len({p["match"] for p in combo}) != sz: continue

            # Max 2 Over1.5, max 2 Over2.5, max 2 GG
            mc = {}
            for p in combo: mc[p["market"]] = mc.get(p["market"], 0) + 1
            if any(v > 2 for v in mc.values()): continue

            tot = math.prod(p["odds"] for p in combo)
            if tot < target * 0.55 or tot > target * 1.55: continue

            combo_prob   = math.prod(p["prob"] for p in combo)
            diff_penalty = abs(tot - target) / target
            score = combo_prob * 70 + sum(p["edge"] for p in combo) * 15 - diff_penalty * 15

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
    target   = float(body.get("target", 3))

    if not odds_key:
        return jsonify({"error": "Odds API key mancante"}), 400

    cfg = get_cfg(target)

    now_utc = datetime.now(timezone.utc)
    italy_offset = 2 if now_utc.month in [4,5,6,7,8,9,10] else 1
    italy_tz = timezone(timedelta(hours=italy_offset))
    now_italy = now_utc.astimezone(italy_tz)
    today_end_utc = now_italy.replace(hour=23, minute=59, second=59).astimezone(timezone.utc)

    all_picks, leagues_found = [], []

    for lg in LEAGUES:
        try:
            url = (f"https://api.the-odds-api.com/v4/sports/{lg['key']}/odds/"
                   f"?apiKey={odds_key}&regions=eu&markets=totals,btts&oddsFormat=decimal")
            r = requests.get(url, timeout=8)
            if not r.ok: continue
            events = r.json()
            if not isinstance(events, list) or not events: continue

            today_events = []
            for ev in events:
                ct = ev.get("commence_time", "")
                if not ct: continue
                try:
                    t = datetime.fromisoformat(ct.replace("Z", "+00:00"))
                    if now_utc <= t <= today_end_utc:
                        today_events.append(ev)
                except: continue

            if not today_events: continue
            leagues_found.append(lg["name"])
            for ev in today_events:
                all_picks.extend(analyze_event(ev, lg, fd_key))
        except: continue
        if len(all_picks) >= 100: break

    if not all_picks:
        return jsonify({"error": f"Nessuna partita trovata per oggi ({now_italy.strftime('%d/%m/%Y')})."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    combo = find_best_combo(unique, target, cfg)

    if not combo:
        return jsonify({"error": "Impossibile costruire una multipla. Riprova tra qualche ora."}), 404

    total_odds   = round(math.prod(p["odds"] for p in combo), 2)
    combo_prob   = round(math.prod(p["prob"] for p in combo) * 100, 1)
    value_count  = sum(1 for p in combo if p["edge"] > 0.02)

    return jsonify({
        "total_odds":        total_odds,
        "combo_probability": combo_prob,
        "picks":             combo,
        "leagues_with_data": len(leagues_found),
        "matches_analyzed":  len({p["match"] for p in unique}),
        "value_bets_found":  sum(1 for p in unique if p["edge"] > 0.02),
        "value_in_combo":    value_count,
        "football_api_used": fd_key is not None,
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
