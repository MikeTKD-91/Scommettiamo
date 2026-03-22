from flask import Flask, request, jsonify
from flask_cors import CORS
import requests, math, itertools, os

app = Flask(__name__)
CORS(app)

LEAGUES = [
    {"key": "soccer_epl",                    "name": "Premier League",   "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fb_id": 39},
    {"key": "soccer_italy_serie_a",          "name": "Serie A",          "flag": "🇮🇹",  "fb_id": 135},
    {"key": "soccer_spain_la_liga",          "name": "La Liga",          "flag": "🇪🇸",  "fb_id": 140},
    {"key": "soccer_germany_bundesliga",     "name": "Bundesliga",       "flag": "🇩🇪",  "fb_id": 78},
    {"key": "soccer_france_ligue_one",       "name": "Ligue 1",          "flag": "🇫🇷",  "fb_id": 61},
    {"key": "soccer_efl_champ",              "name": "Championship",     "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fb_id": 40},
    {"key": "soccer_italy_serie_b",          "name": "Serie B",          "flag": "🇮🇹",  "fb_id": 136},
    {"key": "soccer_spain_segunda_division", "name": "La Liga 2",        "flag": "🇪🇸",  "fb_id": 141},
    {"key": "soccer_germany_bundesliga2",    "name": "Bundesliga 2",     "flag": "🇩🇪",  "fb_id": 79},
    {"key": "soccer_uefa_champs_league",     "name": "Champions League", "flag": "🏆",   "fb_id": 2},
    {"key": "soccer_england_league1",        "name": "League One",       "flag": "🏴󠁧󠁢󠁥󠁮󠁧󠁿", "fb_id": 41},
    {"key": "soccer_germany_liga3",          "name": "3. Liga",          "flag": "🇩🇪",  "fb_id": 80},
    {"key": "soccer_portugal_primeira_liga", "name": "Primeira Liga",    "flag": "🇵🇹",  "fb_id": 94},
    {"key": "soccer_netherlands_eredivisie", "name": "Eredivisie",       "flag": "🇳🇱",  "fb_id": 88},
    {"key": "soccer_uefa_europa_league",     "name": "Europa League",    "flag": "🏆",   "fb_id": 3},
]

_cache = {}

# ── Poisson ────────────────────────────────────────────────────────────────────
def pmf(lam, k):
    if lam <= 0: return 0
    return math.exp(k * math.log(lam) - lam - sum(math.log(i) for i in range(1, k+1)))

def poisson_probs(lh, la):
    o15 = o25 = gg = u25 = 0.0
    for h in range(9):
        for a in range(9):
            p = pmf(lh, h) * pmf(la, a)
            t = h + a
            if t > 1.5: o15 += p
            if t > 2.5: o25 += p
            if t <= 2.5: u25 += p
            if h > 0 and a > 0: gg += p
    return {"over15": min(o15,.99), "over25": min(o25,.99), "under25": min(u25,.99), "gg": min(gg,.99)}

def win_probs(lh, la, hf, af):
    hw = aw = dr = 0.0
    for h in range(9):
        for a in range(9):
            p = pmf(lh, h) * pmf(la, a)
            if h > a: hw += p
            elif a > h: aw += p
            else: dr += p
    hw *= (0.7 + 0.6 * hf)
    aw *= (0.7 + 0.6 * af)
    tot = hw + aw + dr
    return hw/tot, aw/tot, dr/tot

# ── API-Football ───────────────────────────────────────────────────────────────
def get_stats(name, league_id, fb_key):
    ck = f"{name}_{league_id}"
    if ck in _cache: return _cache[ck]
    try:
        h = {"x-apisports-key": fb_key}
        teams = requests.get(f"https://v3.football.api-sports.io/teams?name={requests.utils.quote(name)}", headers=h, timeout=5).json().get("response", [])
        if not teams: return None
        tid = teams[0]["team"]["id"]
        s = requests.get(f"https://v3.football.api-sports.io/teams/statistics?team={tid}&league={league_id}&season=2024", headers=h, timeout=5).json().get("response")
        if not s: return None
        pl   = s["fixtures"]["played"]["total"] or 1
        pl_h = s["fixtures"]["played"]["home"]  or 1
        pl_a = s["fixtures"]["played"]["away"]  or 1
        res = {
            "avg_for_h":      (s["goals"]["for"]["total"]["home"]     or 0) / pl_h,
            "avg_for_a":      (s["goals"]["for"]["total"]["away"]     or 0) / pl_a,
            "avg_against_h":  (s["goals"]["against"]["total"]["home"] or 0) / pl_h,
            "avg_against_a":  (s["goals"]["against"]["total"]["away"] or 0) / pl_a,
            "form": s.get("form", ""),
        }
        _cache[ck] = res
        return res
    except: return None

def form_score(form):
    if not form: return 0.5
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in form[-5:]) / 15

# ── Analyze ────────────────────────────────────────────────────────────────────
def analyze(event, league, fb_key):
    home, away = event["home_team"], event["away_team"]
    avg = 1.35
    hs = get_stats(home, league["fb_id"], fb_key) if fb_key else None
    as_ = get_stats(away, league["fb_id"], fb_key) if fb_key else None

    lh = hs["avg_for_h"] * (as_["avg_against_a"]/avg if as_ else 1) if hs else avg
    la = as_["avg_for_a"] * (hs["avg_against_h"]/avg if hs else 1) if as_ else avg
    lh = max(0.3, min(4.0, lh))
    la = max(0.3, min(4.0, la))

    pr   = poisson_probs(lh, la)
    hf   = form_score(hs["form"] if hs else "")
    af   = form_score(as_["form"] if as_ else "")
    exp_g = round(lh + la, 2)

    picks = []
    for bk in event.get("bookmakers", []):
        markets = {m["key"]: m for m in bk.get("markets", [])}

        if "h2h" in markets:
            outs = {o["name"]: float(o["price"]) for o in markets["h2h"]["outcomes"]}
            ho, ao = outs.get(home), outs.get(away)
            if ho and ao:
                hw, aw, _ = win_probs(lh, la, hf, af)
                if ho <= ao:
                    n, odds, prob = f"Vince {home}", ho, hw
                else:
                    n, odds, prob = f"Vince {away}", ao, aw
                edge = prob - 1/odds
                if 1.15 <= odds <= 4.5:
                    picks.append({"name": n, "odds": round(odds,2), "prob": round(prob,3), "edge": round(edge,3), "market": "h2h", "probs": pr, "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2)})
            break  # one bookmaker for h2h

    for bk in event.get("bookmakers", []):
        markets = {m["key"]: m for m in bk.get("markets", [])}
        if "totals" in markets:
            for o in markets["totals"]["outcomes"]:
                if float(o.get("point", 0)) != 2.5: continue
                odds = float(o["price"])
                is_over = o["name"] == "Over"
                prob = pr["over25"] if is_over else pr["under25"]
                edge = prob - 1/odds
                if 1.2 <= odds <= 5.0:
                    picks.append({"name": f"{o['name']} 2.5", "odds": round(odds,2), "prob": round(prob,3), "edge": round(edge,3), "market": "totals", "probs": pr, "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2)})
            break

    return [{**p, "match": f"{home} vs {away}", "league": f"{league['flag']} {league['name']}", "commence_time": event.get("commence_time"), "score": p["edge"]*40 + (hf+af)*10 + p["prob"]*20} for p in picks]

# ── Combo ──────────────────────────────────────────────────────────────────────
def best_combo(picks, target):
    top = sorted(picks, key=lambda p: p["score"], reverse=True)[:20]
    best, best_diff = [], 9999
    max_sz = 7 if target >= 50 else 5 if target >= 10 else 4 if target >= 5 else 3
    for sz in range(2, max_sz+1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            if len({p["match"] for p in combo}) != sz: continue
            tot = math.prod(p["odds"] for p in combo)
            diff = abs(tot - target)
            if diff < best_diff:
                best_diff = diff
                best = list(combo)
        if best_diff < target * 0.1: break
    return best

# ── Routes ─────────────────────────────────────────────────────────────────────
@app.route("/health")
def health():
    return jsonify({"status": "ok"})

@app.route("/generate", methods=["POST"])
def generate():
    body     = request.get_json() or {}
    odds_key = (body.get("odds_api_key") or "").strip()
    fb_key   = (body.get("football_api_key") or "").strip() or None
    target   = float(body.get("target", 3))

    if not odds_key:
        return jsonify({"error": "Odds API key mancante"}), 400

    all_picks, leagues_found = [], []

    for lg in LEAGUES:
        try:
            url = f"https://api.the-odds-api.com/v4/sports/{lg['key']}/odds/?apiKey={odds_key}&regions=eu&markets=h2h,totals&oddsFormat=decimal"
            r = requests.get(url, timeout=8)
            if not r.ok: continue
            events = r.json()
            if not isinstance(events, list) or not events: continue
            leagues_found.append(lg["name"])
            for ev in events:
                all_picks.extend(analyze(ev, lg, fb_key))
        except:
            continue
        if len(all_picks) >= 80: break

    if not all_picks:
        return jsonify({"error": "Nessuna quota trovata. Controlla la Odds API key."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    combo = best_combo(unique, target)
    if not combo:
        return jsonify({"error": "Impossibile costruire una multipla valida."}), 404

    return jsonify({
        "total_odds": round(math.prod(p["odds"] for p in combo), 2),
        "picks": combo,
        "leagues_with_data": len(leagues_found),
        "matches_analyzed": len({p["match"] for p in unique}),
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
