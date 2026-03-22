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

_stats_cache = {}
_team_id_cache = {}

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

def get_fd_headers(fd_key):
    return {"X-Auth-Token": fd_key}

def load_team_ids(fd_code, fd_key):
    """Carica tutti i team ID di una competizione in una sola chiamata"""
    if fd_code in _team_id_cache:
        return _team_id_cache[fd_code]
    try:
        r = requests.get(
            f"https://api.football-data.org/v4/competitions/{fd_code}/teams",
            headers=get_fd_headers(fd_key), timeout=8
        )
        if not r.ok: return {}
        teams = r.json().get("teams", [])
        mapping = {}
        for t in teams:
            mapping[t["name"].lower()] = t["id"]
            mapping[t["shortName"].lower()] = t["id"]
            if t.get("tla"):
                mapping[t["tla"].lower()] = t["id"]
        _team_id_cache[fd_code] = mapping
        return mapping
    except:
        return {}

def find_team_id(name, fd_code, fd_key):
    mapping = load_team_ids(fd_code, fd_key)
    nl = name.lower()
    # Cerca match esatto
    if nl in mapping:
        return mapping[nl]
    # Cerca match parziale
    for k, v in mapping.items():
        if nl in k or k in nl:
            return v
    return None

def get_stats(name, fd_code, fd_key):
    if not fd_code: return None
    ck = f"{name}_{fd_code}"
    if ck in _stats_cache: return _stats_cache[ck]
    try:
        team_id = find_team_id(name, fd_code, fd_key)
        if not team_id: return None

        # Prendi le ultime partite del team
        r = requests.get(
            f"https://api.football-data.org/v4/teams/{team_id}/matches?status=FINISHED&limit=10",
            headers=get_fd_headers(fd_key), timeout=8
        )
        if not r.ok: return None
        matches = r.json().get("matches", [])
        if not matches: return None

        goals_for_h = goals_for_a = goals_against_h = goals_against_a = 0
        played_h = played_a = 0
        form = ""

        for m in matches:
            home_team = m["homeTeam"]["name"]
            score = m["score"]["fullTime"]
            gh = score.get("home", 0) or 0
            ga = score.get("away", 0) or 0
            is_home = home_team.lower() == name.lower() or name.lower() in home_team.lower()

            if is_home:
                goals_for_h += gh
                goals_against_h += ga
                played_h += 1
                if gh > ga: form += "W"
                elif gh == ga: form += "D"
                else: form += "L"
            else:
                goals_for_a += ga
                goals_against_a += gh
                played_a += 1
                if ga > gh: form += "W"
                elif ga == gh: form += "D"
                else: form += "L"

        res = {
            "avg_for_h":     goals_for_h / played_h if played_h > 0 else 1.35,
            "avg_for_a":     goals_for_a / played_a if played_a > 0 else 1.35,
            "avg_against_h": goals_against_h / played_h if played_h > 0 else 1.35,
            "avg_against_a": goals_against_a / played_a if played_a > 0 else 1.35,
            "form": form[-10:],
        }
        _stats_cache[ck] = res
        return res
    except:
        return None

def form_score(form):
    if not form: return 0.5
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in form[-5:]) / 15

def analyze(event, league, fd_key):
    home, away = event["home_team"], event["away_team"]
    avg = 1.35
    fd_code = league.get("fd_code")
    hs  = get_stats(home, fd_code, fd_key) if fd_key and fd_code else None
    as_ = get_stats(away, fd_code, fd_key) if fd_key and fd_code else None

    lh = hs["avg_for_h"] * (as_["avg_against_a"]/avg if as_ else 1) if hs else avg
    la = as_["avg_for_a"] * (hs["avg_against_h"]/avg if hs else 1) if as_ else avg
    lh = max(0.3, min(4.0, lh))
    la = max(0.3, min(4.0, la))

    pr    = poisson_probs(lh, la)
    hf    = form_score(hs["form"] if hs else "")
    af    = form_score(as_["form"] if as_ else "")
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
            break

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

@app.route("/health")
def health():
    return jsonify({"status": "ok"})

@app.route("/test-fd")
def test_fd():
    key = request.args.get("key", "")
    name = request.args.get("name", "Atalanta")
    fd_code = request.args.get("league", "SA")
    if not key:
        return jsonify({"error": "Aggiungi ?key=LA_TUA_KEY"})
    team_id = find_team_id(name, fd_code, key)
    if not team_id:
        ids = load_team_ids(fd_code, key)
        return jsonify({"error": f"'{name}' non trovata", "available": list(ids.keys())[:20]})
    stats = get_stats(name, fd_code, key)
    return jsonify({
        "searched": name,
        "team_id": team_id,
        "stats": stats,
    })

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
    today_end_utc = now_italy.replace(hour=23, minute=59, second=59).astimezone(timezone.utc)

    all_picks, leagues_found = [], []

    for lg in LEAGUES:
        try:
            url = f"https://api.the-odds-api.com/v4/sports/{lg['key']}/odds/?apiKey={odds_key}&regions=eu&markets=h2h,totals&oddsFormat=decimal"
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
                except:
                    continue

            if not today_events: continue
            leagues_found.append(lg["name"])
            for ev in today_events:
                all_picks.extend(analyze(ev, lg, fd_key))
        except:
            continue
        if len(all_picks) >= 80: break

    if not all_picks:
        return jsonify({"error": f"Nessuna partita trovata per oggi ({now_italy.strftime('%d/%m/%Y')})."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    combo = best_combo(unique, target)
    if not combo:
        return jsonify({"error": "Impossibile costruire una multipla valida."}), 404

    stats_count = sum(1 for p in combo if p.get("home_form", 0.5) != 0.5 or p.get("away_form", 0.5) != 0.5)

    return jsonify({
        "total_odds": round(math.prod(p["odds"] for p in combo), 2),
        "picks": combo,
        "leagues_with_data": len(leagues_found),
        "matches_analyzed": len({p["match"] for p in unique}),
        "football_api_used": fd_key is not None,
        "picks_with_real_stats": stats_count,
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
