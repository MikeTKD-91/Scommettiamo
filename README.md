# ⚽ Salvadanaio Quota 3

Sistema di analisi statistica professionale per scommesse calcio.
Usa **distribuzione di Poisson**, xG, forma recente, casa/trasferta e Value Bet.

---

## 📁 Struttura

```
salvadanaio/
├── backend/          → Deploy su Railway
│   ├── main.py       → Server Flask (Poisson, analisi, API)
│   ├── requirements.txt
│   └── Procfile
└── frontend/         → Deploy su GitHub Pages
    └── index.html    → Interfaccia completa
```

---

## 🚀 Deploy in 3 passi

### PASSO 1 — Backend su Railway

1. Vai su [railway.app](https://railway.app) → **New Project** → **Deploy from GitHub repo**
2. Seleziona il tuo repo
3. Railway chiede la **Root Directory** → scrivi: `backend`
4. Aspetta il deploy (2-3 minuti)
5. Vai su **Settings** → **Networking** → **Generate Domain**
6. Copia l'URL (es: `https://salvadanaio-production.up.railway.app`)

### PASSO 2 — Frontend su GitHub Pages

1. Su GitHub → **Settings** → **Pages**
2. Source: `main` branch → cartella `/frontend`
3. Dopo 1 minuto il sito è online su `tuonome.github.io/nomerepo`

### PASSO 3 — Configura il sito

1. Apri il sito su GitHub Pages
2. Incolla il **Backend URL** di Railway nel primo campo
3. Incolla la tua **Odds API key**
4. (Opzionale) Incolla la **API-Football key** per statistiche avanzate
5. Scegli la **Quota Target** e premi **Genera Multipla** ✅

---

## 🔑 API Keys

- **The Odds API** (obbligatoria): [the-odds-api.com](https://the-odds-api.com)
- **API-Football** (opzionale, migliora i calcoli): [api-football.com](https://www.api-football.com)

Le chiavi vengono salvate solo nel browser — non vengono mai mandate al backend.

---

## 📊 Come funziona l'analisi

1. **Fetch quote** → The Odds API (15 campionati, h2h + totals)
2. **Statistiche squadre** → API-Football (media gol casa/trasferta, forma)
3. **Distribuzione di Poisson** → calcola λ incrociati (attacco vs difesa avversaria)
4. **Probabilità** → Over 1.5/2.5, Goal/Goal, esito partita
5. **Value Bet** → confronto prob. reale vs quota implicita del bookmaker
6. **Combinazione ottimale** → algoritmo che trova i pick con score più alto vicini alla quota target
