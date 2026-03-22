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

# Quota range per target — quote basse = più sicurezza
TARGET_CONFIG = {
    3:   {"min_odds": 1.25, "max_odds": 1.65, "min_picks": 2, "max_picks": 3},
    5:   {"min_odds": 1.30, "max_odds": 1.75, "min_picks": 3, "max_picks": 4},
    8:   {"min_odds": 1.35, "max_odds": 1.90, "min_picks": 3, "max_picks": 5},
    10:  {"min_odds": 1.40, "max_odds": 2.00, "min_picks": 4, "max_picks": 5},
    100: {"min_odds": 1.50, "max_odds": 3.50, "min_picks": 5, "max_picks": 8},
}

def get_target_config(target):
    keys = sorted(TARGET_CONFIG.keys())
    for k in keys:
        if target <= k:
            return TARGET_CONFIG[k]
    return TARGET_CONFIG[100]

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
    if nl in mapping: return mapping[nl]
    for k, v in mapping.items():
        if nl in k or k in nl: return v
    return None

def get_stats(name, fd_code, fd_key):
    if not fd_code: return None
    ck = f"{name}_{fd_code}"
    if ck in _stats_cache: return _stats_cache[ck]
    try:
        team_id = find_team_id(name, fd_code, fd_key)
        if not team_id: return None
        r = requests.get(
            f"https://api.football-data.org/v4/teams/{team_id}/matches?status=FINISHED&limit=10",
            headers=get_fd_headers(fd_key), timeout=8
        )
        if not r.ok: return None
        matches = r.json().get("matches", [])
        if not matches: return None

        gfh = gfa = gah = gaa = 0
        ph = pa = 0
        form = ""

        for m in matches:
            home_team = m["homeTeam"]["name"]
            score = m["score"]["fullTime"]
            gh = score.get("home", 0) or 0
            ga = score.get("away", 0) or 0
            is_home = name.lower() in home_team.lower() or home_team.lower() in name.lower()

            if is_home:
                gfh += gh; gah += ga; ph += 1
                form += "W" if gh > ga else "D" if gh == ga else "L"
            else:
                gfa += ga; gaa += gh; pa += 1
                form += "W" if ga > gh else "D" if ga == gh else "L"

        res = {
            "avg_for_h":     gfh / ph if ph > 0 else 1.35,
            "avg_for_a":     gfa / pa if pa > 0 else 1.35,
            "avg_against_h": gah / ph if ph > 0 else 1.35,
            "avg_against_a": gaa / pa if pa > 0 else 1.35,
            "form": form[-10:],
            "has_real_stats": True,
        }
        _stats_cache[ck] = res
        return res
    except:
        return None

def form_score(form):
    if not form: return 0.5
    return sum(3 if c=="W" else 1 if c=="D" else 0 for c in form[-5:]) / 15

def analyze(event, league, fd_key, cfg):
    home, away = event["home_team"], event["away_team"]
    avg = 1.35
    fd_code = league.get("fd_code")
    hs  = get_stats(home, fd_code, fd_key) if fd_key and fd_code else None
    as_ = get_stats(away, fd_code, fd_key) if fd_key and fd_code else None

    # Se non abbiamo stats reali e fd_key è presente, skippa la partita
    # (evita pick con 50/50 quando dovremmo avere dati)
    has_real = (hs is not None and hs.get("has_real_stats")) or \
               (as_ is not None and as_.get("has_real_stats"))
    if fd_key and fd_code and not has_real:
        return []

    lh = hs["avg_for_h"] * (as_["avg_against_a"]/avg if as_ else 1) if hs else avg
    la = as_["avg_for_a"] * (hs["avg_against_h"]/avg if hs else 1) if as_ else avg
    lh = max(0.3, min(4.0, lh))
    la = max(0.3, min(4.0, la))

    pr    = poisson_probs(lh, la)
    hf    = form_score(hs["form"] if hs else "")
    af    = form_score(as_["form"] if as_ else "")
    exp_g = round(lh + la, 2)

    min_odds = cfg["min_odds"]
    max_odds = cfg["max_odds"]
    picks = []

    # H2H — solo favorito netto
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
                # Solo VALUE BET con quote nel range target
                if min_odds <= odds <= max_odds and edge > 0.02:
                    picks.append({
                        "name": n, "odds": round(odds,2), "prob": round(prob,3),
                        "edge": round(edge,3), "market": "h2h", "probs": pr,
                        "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                    })
            break

    # Totals
    for bk in event.get("bookmakers", []):
        markets = {m["key"]: m for m in bk.get("markets", [])}
        if "totals" in markets:
            for o in markets["totals"]["outcomes"]:
                if float(o.get("point", 0)) != 2.5: continue
                odds = float(o["price"])
                is_over = o["name"] == "Over"
                prob = pr["over25"] if is_over else pr["under25"]
                edge = prob - 1/odds
                # Solo VALUE BET con quote nel range target
                if min_odds <= odds <= max_odds and edge > 0.02:
                    picks.append({
                        "name": f"{o['name']} 2.5", "odds": round(odds,2), "prob": round(prob,3),
                        "edge": round(edge,3), "market": "totals", "probs": pr,
                        "exp_g": exp_g, "home_form": round(hf,2), "away_form": round(af,2),
                        "has_real_stats": has_real,
                    })
            break

    return [{
        **p,
        "match": f"{home} vs {away}",
        "league": f"{league['flag']} {league['name']}",
        "commence_time": event.get("commence_time"),
        # Score: priorità a edge alto, probabilità alta, stats reali
        "score": p["edge"]*50 + p["prob"]*30 + (hf+af)*10 + (10 if has_real else 0),
    } for p in picks]

def best_combo(picks, target, cfg):
    """
    Trova la combinazione migliore:
    1. Solo VALUE BET (già filtrati)
    2. Mercati diversi (no 3 Over insieme)
    3. Numero pick nel range del target
    4. Quota totale più vicina al target
    5. Probabilità combinata più alta possibile
    """
    # Ordina per score
    top = sorted(picks, key=lambda p: p["score"], reverse=True)[:25]
    best, best_score = [], -1

    min_sz = cfg["min_picks"]
    max_sz = cfg["max_picks"]

    for sz in range(min_sz, max_sz+1):
        if len(top) < sz: continue
        for combo in itertools.combinations(top, sz):
            # No partite duplicate
            if len({p["match"] for p in combo}) != sz: continue

            # Diversità mercati — max 2 dello stesso mercato
            market_counts = {}
            for p in combo:
                market_counts[p["market"]] = market_counts.get(p["market"], 0) + 1
            if any(v > 2 for v in market_counts.values()): continue

            tot = math.prod(p["odds"] for p in combo)

            # Deve essere ragionevolmente vicina al target (±40%)
            if tot < target * 0.6 or tot > target * 1.4: continue

            # Probabilità combinata
            combo_prob = math.prod(p["prob"] for p in combo)

            # Score combinato: prob alta + vicino al target + edge totale
            diff_penalty = abs(tot - target) / target
            combo_score = combo_prob * 60 + sum(p["edge"] for p in combo) * 20 - diff_penalty * 20

            if combo_score > best_score:
                best_score = combo_score
                best = list(combo)

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

    cfg = get_target_config(target)

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
                all_picks.extend(analyze(ev, lg, fd_key, cfg))
        except:
            continue
        if len(all_picks) >= 80: break

    if not all_picks:
        # Fallback senza filtro VALUE se non troviamo nulla
        return jsonify({"error": f"Nessun VALUE BET trovato oggi con quota tra {cfg['min_odds']} e {cfg['max_odds']}. Riprova domani o cambia il target."}), 404

    seen, unique = set(), []
    for p in all_picks:
        k = f"{p['match']}|{p['name']}"
        if k not in seen:
            seen.add(k)
            unique.append(p)

    combo = best_combo(unique, target, cfg)

    # Fallback: se non trova combo nel range, allarga la ricerca
    if not combo:
        combo = best_combo(unique, target, {**cfg, "min_picks": 2, "max_picks": cfg["max_picks"]+1})

    if not combo:
        return jsonify({"error": "Impossibile costruire una multipla valida. Pochi VALUE BET disponibili oggi."}), 404

    total_odds = round(math.prod(p["odds"] for p in combo), 2)
    combo_prob = round(math.prod(p["prob"] for p in combo) * 100, 1)

    return jsonify({
        "total_odds": total_odds,
        "combo_probability": combo_prob,
        "picks": combo,
        "leagues_with_data": len(leagues_found),
        "matches_analyzed": len({p["match"] for p in unique}),
        "value_bets_found": len(unique),
        "football_api_used": fd_key is not None,
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
