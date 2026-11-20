#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
agent_betclic.py : rapport Betclic hebdomadaire (foot européen + NBA).

Principe
  1. Cotes Betclic ET Pinnacle via The Odds API (même requête, même coût).
  2. Probabilité estimée = mélange modèle statistique + marché Pinnacle démarginé.
       foot : Dixon-Coles sur 5 saisons football-data.co.uk (gratuit)
       NBA  : Elo avec marge de victoire sur 3 saisons nba_api (gratuit)
  3. Edge = probabilité × cote Betclic − 1. Une sélection n'est retenue que si edge >= EDGE_MIN.
  4. Le rapport HTML est construit par le code : aucun chiffre n'est écrit par une IA.
     Gemini (facultatif) résume seulement les actus blessés pour lever des alertes.

Lancer (PowerShell, dans le dossier qui contient aussi modele_foot_nba.py) :
  python agent_betclic.py --demo        # hors ligne, données simulées -> rapports/rapport_demo.html
  python agent_betclic.py --dry-run     # vraies données, sans envoi d'e-mail
  python agent_betclic.py               # vraies données + e-mail
  Options : --no-llm (pas de Gemini), --jours 4.5

Dépendances : pip install numpy pandas scipy requests nba_api
              pip install tzdata reportlab   (fuseau horaire Windows, PDF)
              facultatif (actus) : pip install google-genai ddgs
"""
from __future__ import annotations

import argparse
import difflib
import html
import io
import itertools
import json
import math
import os
import re
import smtplib
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

from modele_foot_nba import DixonColes, NBAElo, devig_power, markets, score_grid

# =============================================================================
# CONFIGURATION (modifiable par variables d'environnement)
# =============================================================================
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")
API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "")
GMAIL_USER = os.environ.get("GMAIL_USER", "")
GMAIL_APP_PASSWORD = os.environ.get("GMAIL_APP_PASSWORD", "")
GEMINI_MODELS = [m.strip() for m in os.environ.get(
    "GEMINI_MODELS", "gemini-3.8-flash,gemini-3.8-flash-lite,gemma-4-26b-a4b-it,gemma-3-27b-it"
).split(",") if m.strip()]

TZ = ZoneInfo("Europe/Paris")
LIGNES_BUTS = (1.5, 2.5, 3.5)                            # lignes de buts conseillées pour chaque match
COTE_MIN = 1.15                                          # aucune sélection sous cette cote
EDGE_MIN = float((os.environ.get("EDGE_MIN") or "0.03").replace(",", "."))     # value minimale : +3 %
EDGE_SUSPECT = 0.15                                      # au-delà : erreur probable, pas une aubaine
W_MODELE = {"FOOT": 0.35, "BASKET": 0.25}                # poids du modèle face à Pinnacle
KELLY_FRACTION = 0.25
MISE_MAX_PCT = 1.5                                       # plafond de mise en % de bankroll
BANKROLL = float((os.environ.get("BANKROLL") or "0").replace(",", "."))   # facultatif : affiche les mises en euros
CACHE_DIR = Path(os.environ.get("CACHE_DIR", "cache"))
OUT_DIR = Path(os.environ.get("OUT_DIR", "rapports"))
ACTUS_MAX_MATCHS = 12          # actus cherchées seulement pour les matchs qui ont une sélection intéressante
ACTUS_BUDGET_S = 150           # temps maximum consacré aux recherches web

COMPETITIONS = [
    # "equipes" : clubs toujours retenus ; "top_n" : ajoute aussi les clubs classés dans le top N actuel ;
    # "plus_meilleurs" : ajoute les N clubs les mieux classés qui ne sont pas déjà dans "equipes".
    # Un match n'est analysé que s'il implique au moins un club retenu.
    {"id": "soccer_epl", "nom": "Premier League", "cat": "FOOT", "div": "E0", "us": "EPL",
     "equipes": ["Man City", "Arsenal", "Liverpool", "Chelsea", "Tottenham", "Man United"], "top_n": 4},
    {"id": "soccer_spain_la_liga", "nom": "La Liga", "cat": "FOOT", "div": "SP1", "us": "La_Liga",
     "equipes": ["Real Madrid", "Barcelona", "Ath Madrid"], "plus_meilleurs": 1},
    {"id": "soccer_germany_bundesliga", "nom": "Bundesliga", "cat": "FOOT", "div": "D1", "us": "Bundesliga",
     "equipes": ["Bayern Munich", "Leverkusen", "Dortmund"]},
    {"id": "soccer_france_ligue_one", "nom": "Ligue 1", "cat": "FOOT", "div": "F1", "us": "Ligue_1",
     "equipes": ["Paris SG"]},
    {"id": "soccer_uefa_champs_league", "nom": "Ligue des Champions", "cat": "FOOT", "div": None, "ldc": True},
    {"id": "basketball_nba", "nom": "NBA", "cat": "BASKET", "nba": True},
    {"id": "basketball_euroleague", "nom": "EuroLeague", "cat": "BASKET"},
]

# Italie : aucun championnat italien, jamais (verrou, même si quelqu'un l'ajoute à la liste ci-dessus).
SPORTS_INTERDITS = ("soccer_italy",)
# Clubs italiens en Ligue des Champions : gardés par défaut (la règle vise le championnat). Mets True pour les retirer.
EXCLURE_ITALIENS_LDC = (os.environ.get("EXCLURE_ITALIENS_LDC") or "").lower() in ("1", "true", "oui")
CLUBS_ITALIENS = ["Inter Milan", "Internazionale", "AC Milan", "Milan", "Juventus", "Napoli", "Atalanta",
                  "Atalanta BC", "AS Roma", "Roma", "Lazio", "Bologna", "Fiorentina", "Como", "Torino"]

# Noms The Odds API / Understat / ESPN -> noms football-data / nba_api.
# Si le rapport signale "équipe non reconnue", ajoute la correspondance ici.
ALIASES_RAW = {
    "Manchester United": "Man United", "Manchester City": "Man City", "Newcastle United": "Newcastle",
    "Nottingham Forest": "Nott'm Forest", "Tottenham Hotspur": "Tottenham", "West Ham United": "West Ham",
    "Wolverhampton Wanderers": "Wolves", "Brighton and Hove Albion": "Brighton", "Leeds United": "Leeds",
    "AFC Bournemouth": "Bournemouth", "Sunderland AFC": "Sunderland",
    "Athletic Bilbao": "Ath Bilbao", "Athletic Club": "Ath Bilbao", "Atlético Madrid": "Ath Madrid",
    "Atletico Madrid": "Ath Madrid", "Real Sociedad": "Sociedad", "Real Betis": "Betis",
    "Celta Vigo": "Celta", "Rayo Vallecano": "Vallecano", "Deportivo Alavés": "Alaves",
    "Espanyol": "Espanol", "RCD Mallorca": "Mallorca", "Real Oviedo": "Oviedo",
    "Borussia Dortmund": "Dortmund", "Bayer Leverkusen": "Leverkusen", "Eintracht Frankfurt": "Ein Frankfurt",
    "Borussia Monchengladbach": "M'gladbach", "Borussia Mönchengladbach": "M'gladbach",
    "1. FSV Mainz 05": "Mainz", "FSV Mainz 05": "Mainz", "VfB Stuttgart": "Stuttgart",
    "VfL Wolfsburg": "Wolfsburg", "SV Werder Bremen": "Werder Bremen", "TSG Hoffenheim": "Hoffenheim",
    "SC Freiburg": "Freiburg", "FC Augsburg": "Augsburg", "1. FC Union Berlin": "Union Berlin",
    "FC St. Pauli": "St Pauli", "1. FC Heidenheim": "Heidenheim", "1. FC Köln": "FC Koln",
    "FC Cologne": "FC Koln", "Hamburger SV": "Hamburg", "RasenBallsport Leipzig": "RB Leipzig",
    "Paris Saint Germain": "Paris SG", "Paris Saint-Germain": "Paris SG", "Olympique Marseille": "Marseille",
    "Olympique Lyonnais": "Lyon", "AS Monaco": "Monaco", "OGC Nice": "Nice", "RC Lens": "Lens",
    "Stade Rennais": "Rennes", "RC Strasbourg": "Strasbourg", "FC Nantes": "Nantes",
    "Stade Brestois 29": "Brest", "AJ Auxerre": "Auxerre", "Le Havre AC": "Le Havre",
    "Los Angeles Clippers": "LA Clippers",
    "FC Barcelona": "Barcelona", "Barça": "Barcelona", "Bayern München": "Bayern Munich",
    "FC Bayern Munich": "Bayern Munich", "FC Bayern München": "Bayern Munich", "Real Madrid CF": "Real Madrid",
    "Club Atlético de Madrid": "Ath Madrid", "Atletico de Madrid": "Ath Madrid",
    "Man Utd": "Man United", "Spurs": "Tottenham", "Nottingham": "Nott'm Forest", "Atletico Madrid": "Ath Madrid",
    "Paris Saint-Germain FC": "Paris SG", "PSG": "Paris SG", "Borussia Monchengladbach FC": "M'gladbach",
}


def log(msg: str) -> None:
    print(f"[{datetime.now():%H:%M:%S}] {msg}", flush=True)


# =============================================================================
# CORRESPONDANCE DES NOMS D'ÉQUIPES (chaque source a les siens)
# =============================================================================
def norm(s: str) -> str:
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode().lower()
    s = re.sub(r"[^a-z0-9 ]+", " ", s.replace("'", " "))
    return " ".join(s.split())


ALIASES = {norm(k): v for k, v in ALIASES_RAW.items()}


def canon(s: str) -> str:
    n = norm(s)
    return norm(ALIASES.get(n, n))


def match_team(name: str, candidates) -> str | None:
    """Renvoie le nom de `candidates` qui correspond à `name`, ou None."""
    cmap = {canon(c): c for c in candidates}
    n = canon(name)
    if n in cmap:
        return cmap[n]
    for k, c in cmap.items():
        if len(k) >= 4 and len(n) >= 4 and (k in n or n in k):
            return c
    best = difflib.get_close_matches(n, list(cmap), n=1, cutoff=0.78)
    return cmap[best[0]] if best else None


# =============================================================================
# SOURCES RÉELLES
# =============================================================================
UA = {"User-Agent": "Mozilla/5.0 (compatible; agent-betclic/2.0)"}
UA_NAV = {"User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                         "Chrome/131.0.0.0 Safari/537.36"),
          "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.8"}


def avec_delai(fn, secondes, *args, relancer=False, **kwargs):
    """Exécute fn avec un délai maximum : renvoie None si trop long (le fil est abandonné).
    Avec relancer=True, une exception de fn est remontée ; sinon elle donne None."""
    import threading
    res = {}

    def cible():
        try:
            res["v"] = fn(*args, **kwargs)
        except Exception as ex:
            res["e"] = ex

    t = threading.Thread(target=cible, daemon=True)
    t.start()
    t.join(secondes)
    if t.is_alive():
        return None
    if "e" in res:
        if relancer:
            raise res["e"]
        return None
    return res.get("v")


def http_get(url, params=None, headers=None, timeout=25, retries=2):
    h = dict(UA)
    h.update(headers or {})
    for i in range(retries + 1):
        try:
            r = requests.get(url, params=params, headers=h, timeout=timeout)
            if r.status_code == 200:
                return r
            log(f"HTTP {r.status_code} sur {url.split('?')[0]}")
            if r.status_code in (401, 403, 404, 422, 429):
                return None
        except requests.RequestException as e:
            log(f"Erreur réseau {url.split('?')[0]} : {e}")
        time.sleep(2 * (i + 1))
    return None


def cached_bytes(url: str, name: str, max_age_h: float = 12, headers=None):
    CACHE_DIR.mkdir(exist_ok=True)
    f = CACHE_DIR / name
    if f.exists() and (time.time() - f.stat().st_mtime) < max_age_h * 3600:
        return f.read_bytes()
    r = http_get(url, headers=headers)
    if r is None:
        return f.read_bytes() if f.exists() else None  # un cache périmé vaut mieux que rien
    f.write_bytes(r.content)
    return r.content


def parse_event(ev: dict) -> dict:
    home, away = ev["home_team"], ev["away_team"]
    out = {
        "id": ev.get("id") or f"{home}|{away}",
        "home": home, "away": away,
        "start": datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00")),
        "betclic": {"h2h": {}, "totals": {}},
        "pinnacle": {"h2h": {}, "totals": {}},
    }
    for bk in ev.get("bookmakers", []):
        key = bk.get("key")
        cible = out["betclic"] if key == "betclic_fr" else out["pinnacle"] if key == "pinnacle" else None
        if cible is None:
            continue
        for m in bk.get("markets", []):
            if m.get("key") == "h2h":
                for o in m.get("outcomes", []):
                    k = "H" if o["name"] == home else "A" if o["name"] == away else "D" if o["name"] == "Draw" else None
                    if k:
                        cible["h2h"][k] = float(o["price"])
            elif m.get("key") == "totals":
                for o in m.get("outcomes", []):
                    if o.get("point") is not None:
                        cible["totals"].setdefault(float(o["point"]), {})[o["name"]] = float(o["price"])
    return out


class SourcesReelles:
    demo = False

    def __init__(self, use_llm: bool = True):
        self.use_llm = use_llm
        self.quota = "?"
        self.echecs: list[str] = []
        self.apifoot = APIFoot(self.echecs)
        self._fpl = False

    def fpl(self):
        if self._fpl is False:
            self._fpl = fpl_joueurs()
            if self._fpl is None:
                self.echecs.append("Fantasy Premier League indisponible (blessures Angleterre)")
        return self._fpl

    def _joueurs_secours(self, comp, now):
        """Si Understat bloque : Fantasy Premier League (Angleterre) ou meilleurs buteurs API-Football."""
        if comp["id"] == "soccer_epl" and self.fpl() is not None:
            j = self.fpl()
            return j[j["time"] > 0][["joueur", "team", "games", "time", "goals", "xG"]].copy()
        ligue = LIGUES_APIFOOT.get(comp["id"])
        if ligue and self.apifoot.ok:
            df = buteurs_apifoot(self.apifoot, ligue, now)
            if df is not None:
                return df[["joueur", "team", "games", "time", "goals", "xG"]]
        return None

    # ---- cotes ----
    def cotes(self, comp):
        if not ODDS_API_KEY:
            self.echecs.append("ODDS_API_KEY absente")
            return []
        r = http_get(
            f"https://api.the-odds-api.com/v4/sports/{comp['id']}/odds/",
            params={"apiKey": ODDS_API_KEY, "regions": "eu", "markets": "h2h,totals",
                    "bookmakers": "betclic_fr,pinnacle", "oddsFormat": "decimal"},
        )
        if r is None:
            self.echecs.append(f"Cotes {comp['nom']}")
            return []
        self.quota = r.headers.get("x-requests-remaining", self.quota)
        out = []
        for ev in r.json():
            try:
                out.append(parse_event(ev))
            except Exception:
                continue
        return out

    # ---- historique foot : football-data.co.uk, 5 saisons ----
    def historique_foot(self, comp, now):
        memo = self.__dict__.setdefault("_hist", {})
        if comp["div"] not in memo:
            memo[comp["div"]] = self._historique_foot(comp, now)
        return memo[comp["div"]]

    def _historique_foot(self, comp, now):
        y0 = now.year if now.month >= 7 else now.year - 1
        frames = []
        for y in range(y0 - 4, y0 + 1):
            code = f"{str(y)[2:]}{str(y + 1)[2:]}"
            raw = cached_bytes(f"https://www.football-data.co.uk/mmz4281/{code}/{comp['div']}.csv",
                               f"fd_{comp['div']}_{code}.csv")
            if raw is None:
                continue
            try:
                frames.append(pd.read_csv(io.BytesIO(raw), encoding="latin-1", on_bad_lines="skip"))
            except Exception as e:
                log(f"CSV illisible {comp['div']} {code} : {e}")
        if not frames:
            self.echecs.append(f"Historique {comp['nom']} (football-data.co.uk)")
            return None
        df = pd.concat(frames, ignore_index=True, sort=False)
        df = df.dropna(subset=["HomeTeam", "AwayTeam", "FTHG", "FTAG", "Date"])
        df["date"] = pd.to_datetime(df["Date"], dayfirst=True, format="mixed", errors="coerce")
        df = df.dropna(subset=["date"]).rename(
            columns={"HomeTeam": "home", "AwayTeam": "away", "FTHG": "hg", "FTAG": "ag"})
        df["hg"] = df["hg"].astype(int)
        df["ag"] = df["ag"].astype(int)
        return df[["date", "home", "away", "hg", "ag"]].sort_values("date").reset_index(drop=True)

    # ---- historique NBA : nba_api, 3 saisons ----
    def games_nba(self, now):
        if getattr(self, "_nba", None) is not None:
            return self._nba
        g = self._nba_api(now)
        if g is None:
            log("   stats.nba.com indisponible : historique NBA récupéré sur ESPN")
            g = self._nba_espn(now)
        if g is None:
            self.echecs.append("Historique NBA (stats.nba.com et ESPN indisponibles) : NBA sur cotes Pinnacle seules")
        self._nba = g
        return g

    def _nba_api(self, now):
        try:
            from nba_api.stats.endpoints import leaguegamelog
        except Exception:
            return None
        y0 = now.year if now.month >= 9 else now.year - 1
        frames = []
        for y in (y0, y0 - 1, y0 - 2):        # saison en cours d'abord : si elle échoue, on passe à ESPN
            saison = f"{y}-{str(y + 1)[2:]}"
            f = CACHE_DIR / f"nba_{saison}.csv"
            if y < y0 and f.exists():           # saisons terminées : cache permanent
                frames.append(pd.read_csv(f))
                continue
            try:
                gl = leaguegamelog.LeagueGameLog(season=saison, season_type_all_star="Regular Season", timeout=25)
                d = gl.get_data_frames()[0]
                CACHE_DIR.mkdir(exist_ok=True)
                d.to_csv(f, index=False)
                frames.append(d)
            except Exception as e:
                log(f"   nba_api {saison} : {str(e)[:80]}")
                if y == y0:
                    return None
            time.sleep(1.5)
        if not frames:
            return None
        df = pd.concat(frames, ignore_index=True)
        df["dom"] = df["MATCHUP"].astype(str).str.contains("vs.", regex=False)
        h = df[df["dom"]][["GAME_ID", "GAME_DATE", "TEAM_NAME", "PTS"]].rename(
            columns={"TEAM_NAME": "home", "PTS": "hpts"})
        a = df[~df["dom"]][["GAME_ID", "TEAM_NAME", "PTS"]].rename(columns={"TEAM_NAME": "away", "PTS": "apts"})
        g = h.merge(a, on="GAME_ID")
        g["date"] = pd.to_datetime(g["GAME_DATE"])
        g["season"] = np.where(g["date"].dt.month >= 9, g["date"].dt.year, g["date"].dt.year - 1)
        return g[["date", "home", "away", "hpts", "apts", "season"]].sort_values("date").reset_index(drop=True)

    def _nba_espn(self, now):
        """Résultats NBA jour par jour via le tableau des scores ESPN (saison passée + en cours), avec cache."""
        CACHE_DIR.mkdir(exist_ok=True)
        f_res, f_jours = CACHE_DIR / "espn_nba.csv", CACHE_DIR / "espn_nba_jours.txt"
        res = (pd.read_csv(f_res, dtype={"jour": str, "eid": str}) if f_res.exists()
               else pd.DataFrame(columns=["jour", "home", "away", "hpts", "apts", "eid"]))
        if "eid" not in res.columns:
            res["eid"] = np.nan
        faits = set(f_jours.read_text().split()) if f_jours.exists() else set()
        hier = now.astimezone(TZ).date() - timedelta(days=1)
        recents = {f"{hier - timedelta(days=k):%Y%m%d}" for k in range(16)}   # feuilles de match utiles : 15 jours
        sans_id = set(res.loc[res["eid"].isna(), "jour"].astype(str)) & recents
        faits -= sans_id
        y0 = now.year if now.month >= 9 else now.year - 1
        jour, a_faire = datetime(y0 - 1, 10, 15).date(), []
        while jour <= hier:
            cle = f"{jour:%Y%m%d}"
            if jour.month not in (7, 8, 9) and (cle not in faits or (hier - jour).days < 3):
                a_faire.append(cle)
            jour += timedelta(days=1)
        if a_faire:
            log(f"   ESPN : {len(a_faire)} journée(s) NBA à récupérer (les suivantes seront en cache)")
        nouveaux, debut, echecs = [], time.time(), 0
        for cle in a_faire:
            if time.time() - debut > 420 or echecs > 15:
                log("   ESPN : arrêt (temps ou erreurs), le reste sera récupéré au prochain lancement")
                break
            r = http_get("https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard",
                         params={"dates": cle, "limit": 100}, timeout=20, retries=1)
            if r is None:
                echecs += 1
                continue
            try:
                for ev in r.json().get("events", []):
                    if (ev.get("season") or {}).get("type") == 1:               # présaison
                        continue
                    if not ((ev.get("status") or {}).get("type") or {}).get("completed"):
                        continue
                    eq = {c.get("homeAway"): c for c in ev["competitions"][0]["competitors"]}
                    nouveaux.append({"jour": cle, "home": eq["home"]["team"]["displayName"],
                                     "away": eq["away"]["team"]["displayName"],
                                     "hpts": int(float(eq["home"]["score"])), "apts": int(float(eq["away"]["score"])),
                                     "eid": str(ev.get("id", ""))})
                faits.add(cle)
            except Exception:
                echecs += 1
            time.sleep(0.15)
        if nouveaux:
            res = pd.concat([res, pd.DataFrame(nouveaux)], ignore_index=True)
            res = res.drop_duplicates(subset=["jour", "home", "away"], keep="last")
            res.to_csv(f_res, index=False)
        f_jours.write_text("\n".join(sorted(faits)))
        if len(res) < 200:
            return None
        g = res.copy()
        g["date"] = pd.to_datetime(g["jour"].astype(str), format="%Y%m%d")
        g["season"] = np.where(g["date"].dt.month >= 9, g["date"].dt.year, g["date"].dt.year - 1)
        return g[["date", "home", "away", "hpts", "apts", "season"]].sort_values("date").reset_index(drop=True)

    # ---- joueurs NBA : match par match (nba_api en un appel, sinon feuilles de match ESPN) ----
    def joueurs_nba(self, now):
        df = self._joueurs_nba_api(now)
        if df is None:
            df = self._joueurs_nba_espn(now)
        if df is None:
            self.echecs.append("Joueurs NBA (nba_api et feuilles de match ESPN indisponibles)")
        return df

    def _joueurs_nba_api(self, now):
        try:
            from nba_api.stats.endpoints import leaguegamelog
        except Exception:
            return None
        y0 = now.year if now.month >= 9 else now.year - 1
        saison = f"{y0}-{str(y0 + 1)[2:]}"
        f = CACHE_DIR / f"nba_joueurs_{saison}.csv"
        if f.exists() and time.time() - f.stat().st_mtime < 6 * 3600:
            d = pd.read_csv(f)
        else:
            try:
                d = avec_delai(lambda: leaguegamelog.LeagueGameLog(
                    season=saison, season_type_all_star="Regular Season", player_or_team_abbreviation="P",
                    timeout=25).get_data_frames()[0], 40)
            except Exception:
                d = None
            if d is None or len(d) == 0:
                return None
            CACHE_DIR.mkdir(exist_ok=True)
            d.to_csv(f, index=False)

        def minutes(x):
            x = str(x)
            if ":" in x:
                mm, ss = x.split(":")[:2]
                return float(mm) + float(ss) / 60
            try:
                return float(x)
            except ValueError:
                return 0.0
        try:
            return pd.DataFrame({"joueur": d["PLAYER_NAME"], "equipe": d["TEAM_NAME"],
                                 "date": pd.to_datetime(d["GAME_DATE"]), "min": d["MIN"].map(minutes), "pts": d["PTS"],
                                 "reb": d["REB"], "ast": d["AST"], "poste": ""})
        except (KeyError, ValueError) as ex:          # format inattendu : on passe aux feuilles de match ESPN
            log(f"   nba_api joueurs : format inattendu ({ex}), passage à ESPN")
            return None

    def _joueurs_nba_espn(self, now):
        g = self.games_nba(now)                       # remplit le cache ESPN (avec les identifiants de match)
        f_res = CACHE_DIR / "espn_nba.csv"
        if not f_res.exists():
            return None
        res = pd.read_csv(f_res, dtype={"eid": str, "jour": str})
        hier = now.astimezone(TZ).date() - timedelta(days=1)
        debut = f"{hier - timedelta(days=15):%Y%m%d}"
        res = res[(res["jour"] >= debut) & res["eid"].notna() & (res["eid"] != "")].drop_duplicates(subset=["eid"])
        rows, dossier, t0 = [], CACHE_DIR / "espn_box", time.time()
        dossier.mkdir(parents=True, exist_ok=True)
        for r in res.itertuples():
            eid = str(r.eid).split(".")[0]
            f = dossier / f"{eid}.json"
            if f.exists():
                data = json.loads(f.read_text(encoding="utf-8"))
            else:
                if time.time() - t0 > 240:
                    break
                rep = http_get("https://site.api.espn.com/apis/site/v2/sports/basketball/nba/summary",
                               params={"event": eid}, timeout=20, retries=1)
                if rep is None:
                    continue
                try:
                    data = rep.json().get("boxscore", {})
                except ValueError:
                    continue
                f.write_text(json.dumps(data), encoding="utf-8")
                time.sleep(0.15)
            rows += lire_feuille_espn(data, r.jour)
        return pd.DataFrame(rows) if rows else None

    # ---- joueurs foot : forme et statistiques de la saison ----
    def joueurs_foot(self, comp, now):
        if comp["id"] == "soccer_epl" and self.fpl() is not None:
            j = self.fpl()
            return j[j["time"] > 0].rename(columns={"team": "equipe", "time": "minutes", "games": "titularisations",
                                                    "goals": "buts"}).assign(mj=lambda x: x["titularisations"])
        ligue = LIGUES_APIFOOT.get(comp["id"])
        if not (ligue and self.apifoot.ok):
            return None
        par_nom = {}
        for it in self.apifoot.meilleurs_buteurs(ligue, now) + self.apifoot.meilleurs_passeurs(ligue, now):
            try:
                st, pl = it["statistics"][0], it["player"]
                cle = (pl["name"], st["team"]["name"])
                par_nom[cle] = {"joueur": pl["name"], "equipe": st["team"]["name"], "age": pl.get("age"),
                                "nationalite": pl.get("nationality") or "",
                                "poste": {"Attacker": "Attaquant", "Midfielder": "Milieu", "Defender": "Défenseur",
                                          "Goalkeeper": "Gardien"}.get(st["games"].get("position"), ""),
                                "mj": float(st["games"].get("appearences") or 0),
                                "minutes": float(st["games"].get("minutes") or 0),
                                "buts": float(st["goals"].get("total") or 0),
                                "passes": float(st["goals"].get("assists") or 0),
                                "note": float(st["games"].get("rating") or 0)}
            except Exception:
                continue
        return pd.DataFrame(list(par_nom.values())) if par_nom else None

    def blessures_nba(self):
        out = {}
        r = http_get("https://site.api.espn.com/apis/site/v2/sports/basketball/nba/injuries")
        if r is None:
            self.echecs.append("Blessures NBA (ESPN)")
            return out
        try:
            for t in r.json().get("injuries", []):
                lst = []
                for i in t.get("injuries", []):
                    nom = (i.get("athlete") or {}).get("displayName", "")
                    st = i.get("status", "")
                    if nom and st:
                        lst.append({"joueur": nom, "statut": st})
                if t.get("displayName") and lst:
                    out[t["displayName"]] = lst
        except Exception:
            pass
        return out

    # ---- buteurs : xG joueurs Understat (6 grands championnats) ----
    def joueurs(self, comp, now):
        slug = comp.get("us")
        if not slug:
            return None
        annee = now.year if now.month >= 7 else now.year - 1
        page = f"https://understat.com/league/{slug}/{annee}"
        try:
            with requests.Session() as ses:
                ses.headers.update(UA_NAV)
                ses.cookies.set("beget", "begetok")
                try:                                  # comme un navigateur : la page d'abord, puis les données
                    ses.get(page, headers={"Accept": "text/html,application/xhtml+xml,*/*;q=0.8"}, timeout=30)
                except requests.RequestException:
                    pass
                r = ses.get(f"https://understat.com/getLeagueData/{slug}/{annee}", timeout=30,
                            headers={"X-Requested-With": "XMLHttpRequest", "Referer": page,
                                     "Accept": "application/json, text/javascript, */*; q=0.01"})
            if r.status_code != 200:
                raise ValueError(f"HTTP {r.status_code}")
            try:
                data = r.json()
            except ValueError:
                extrait = re.sub(r"\s+", " ", r.text[:80]) or "réponse vide"
                raise ValueError(f"réponse non JSON : « {extrait} »")
            df = pd.DataFrame(data.get("players", []))
            if df.empty:
                raise ValueError("aucun joueur dans la réponse")
            for c in ("games", "time", "goals", "xG"):
                df[c] = pd.to_numeric(df[c], errors="coerce")
            df["team"] = df["team_title"].astype(str).str.split(",").str[-1].str.strip()
            df = df.rename(columns={"player_name": "joueur"})
            time.sleep(1)
            return df[["joueur", "team", "games", "time", "goals", "xG"]].dropna()
        except Exception as e:
            try:
                secours = self._joueurs_secours(comp, now)
            except Exception as ex2:
                log(f"   Source de secours des buteurs indisponible ({ex2})")
                secours = None
            if secours is not None:
                log(f"   Understat indisponible pour {comp['nom']} : buteurs pris sur une source de secours")
                return secours
            self.echecs.append(f"Buteurs {comp['nom']} (Understat : {e})")
            return None

    # ---- actus blessés : recherche web + Gemini en simple résumeur ----
    def _gemini(self, prompt: str) -> str:
        from google import genai
        client = genai.Client(api_key=GEMINI_API_KEY)
        for modele in GEMINI_MODELS:
            try:
                rep = avec_delai(client.models.generate_content, 90, model=modele, contents=prompt, relancer=True)
                if rep is not None and rep.text:
                    return rep.text
                log(f"   Gemini {modele} : pas de réponse en 90 s")
            except Exception as e:
                log(f"   Gemini {modele} indisponible ({getattr(e, 'code', e)})")
                time.sleep(3)
        return ""

    def actus(self, items, now):
        """items : [{"id", "home", "away"}] -> {id: {"alerte": bool, "resume": str}}"""
        if not (self.use_llm and GEMINI_API_KEY and items):
            return {}
        try:
            from ddgs import DDGS
            import google.genai  # noqa: F401
        except Exception as e:
            log(f"Actus désactivées : {e}")
            self.echecs.append("Actus blessés (google-genai ou ddgs non installé)")
            return {}
        def chercher(requete):
            with DDGS() as d:
                return list(d.text(requete, max_results=3))

        blocs, debut = [], time.time()
        for i, it in enumerate(items, 1):
            if time.time() - debut > ACTUS_BUDGET_S:
                log(f"   Budget de {ACTUS_BUDGET_S} s atteint : {len(items) - i + 1} match(s) sans actus")
                break
            log(f"   Actus {i}/{len(items)} : {it['home']} – {it['away']}")
            res = avec_delai(chercher, 15, f"{it['home']} {it['away']} injuries suspended predicted lineup") or []
            txt = " | ".join(f"{x.get('title', '')}: {x.get('body', '')}" for x in res)[:700]
            if txt:
                blocs.append({"id": it["id"], "match": f"{it['home']} vs {it['away']}", "extraits": txt})
            time.sleep(1)
        if not blocs:
            self.echecs.append("Actus blessés (recherche web sans résultat)")
            return {}
        log(f"   Résumé des actus par Gemini ({len(blocs)} match(s))")
        prompt = (
            f"Nous sommes le {now:%d/%m/%Y}. Pour chaque match, voici des extraits de recherche web "
            "(parfois anciens ou hors sujet). Indique si les extraits signalent CLAIREMENT l'absence ou le doute "
            "d'un joueur CLÉ pour ce match à venir. N'utilise QUE les extraits, n'invente rien. "
            "Si ce n'est pas clair : alerte=false et resume=\"\". resume : 120 caractères max, en français, "
            "avec le nom du joueur. Réponds UNIQUEMENT par un tableau JSON : "
            '[{"id": "...", "alerte": true, "resume": "..."}]\n\n' + json.dumps(blocs, ensure_ascii=False)
        )
        txt = self._gemini(prompt)
        try:
            data = json.loads(txt[txt.index("["): txt.rindex("]") + 1])
        except Exception:
            log("Réponse Gemini non exploitable : actus ignorées")
            self.echecs.append("Actus blessés (réponse Gemini illisible)")
            return {}
        return {str(d["id"]): {"alerte": bool(d.get("alerte")), "resume": str(d.get("resume", ""))[:140]}
                for d in data if isinstance(d, dict) and "id" in d}


# =============================================================================
# SOURCES DÉMO (hors ligne) : sert à tester toute la chaîne et la mise en page
# =============================================================================
class SourcesDemo:
    demo = True
    CLUBS = {
        "E0": ["Arsenal", "Man City", "Liverpool", "Chelsea", "Tottenham", "Newcastle", "Aston Villa",
               "Brighton", "Man United", "West Ham", "Brentford", "Fulham", "Crystal Palace", "Bournemouth",
               "Everton", "Nott'm Forest", "Wolves", "Leeds", "Burnley", "Sunderland"],
        "SP1": ["Real Madrid", "Barcelona", "Ath Madrid", "Ath Bilbao", "Villarreal", "Betis", "Sociedad",
                "Girona", "Sevilla", "Valencia", "Celta", "Osasuna", "Getafe", "Mallorca", "Vallecano",
                "Alaves", "Espanol", "Elche", "Levante", "Oviedo"],
        "D1": ["Bayern Munich", "Leverkusen", "Dortmund", "RB Leipzig", "Stuttgart", "Ein Frankfurt", "Freiburg",
               "Wolfsburg", "Hoffenheim", "Werder Bremen", "Mainz", "M'gladbach", "Augsburg", "Union Berlin",
               "St Pauli", "Heidenheim", "FC Koln", "Hamburg"],
        "F1": ["Paris SG", "Marseille", "Monaco", "Lens", "Lille", "Lyon", "Nice", "Rennes", "Strasbourg",
               "Toulouse", "Brest", "Nantes", "Auxerre", "Angers", "Le Havre", "Lorient", "Metz", "Paris FC"],
    }
    ODDS_NAMES = {"Man City": "Manchester City", "Man United": "Manchester United", "Ath Madrid": "Atlético Madrid",
                  "Paris SG": "Paris Saint Germain", "Nott'm Forest": "Nottingham Forest", "Lens": "RC Lens",
                  "Leverkusen": "Bayer Leverkusen", "Dortmund": "Borussia Dortmund", "Tottenham": "Tottenham Hotspur"}
    NBA = ["Boston Celtics", "Oklahoma City Thunder", "Cleveland Cavaliers", "Denver Nuggets", "New York Knicks",
           "Houston Rockets", "Los Angeles Lakers", "LA Clippers", "Minnesota Timberwolves", "Indiana Pacers",
           "Golden State Warriors", "Memphis Grizzlies", "Detroit Pistons", "Milwaukee Bucks", "Orlando Magic",
           "Atlanta Hawks", "Dallas Mavericks", "Sacramento Kings", "Miami Heat", "Phoenix Suns",
           "Chicago Bulls", "San Antonio Spurs", "Portland Trail Blazers", "Toronto Raptors",
           "Philadelphia 76ers", "New Orleans Pelicans", "Brooklyn Nets", "Charlotte Hornets",
           "Utah Jazz", "Washington Wizards"]

    def __init__(self, seed=11):
        self.rng = np.random.default_rng(seed)
        self.quota = "démo"
        self.echecs = ["Mode démo : toutes les données sont simulées"]
        self.truth = {}
        self.now = datetime(2026, 11, 20, 13, 0, tzinfo=timezone.utc)

    def _league(self, div):
        if div in self.truth:
            return self.truth[div]
        rng, clubs = self.rng, self.CLUBS[div]
        n = len(clubs)
        att = np.sort(rng.normal(0, 0.3, n))[::-1]
        dfn = np.sort(rng.normal(0, 0.28, n))[::-1] + rng.normal(0, 0.08, n)
        att, dfn = att - att.mean(), dfn - dfn.mean()
        rows, d = [], pd.Timestamp("2022-08-06")
        for s in range(5):
            pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
            order = rng.permutation(len(pairs))
            n_played = len(pairs) if s < 4 else int(len(pairs) * 0.32)  # saison en cours : ~12 journées
            for k in order[:n_played]:
                i, j = pairs[k]
                P = score_grid(np.exp(0.22 + att[i] - dfn[j]), np.exp(att[j] - dfn[i]), -0.07)
                hg, ag = divmod(int(rng.choice(P.size, p=P.ravel())), P.shape[1])
                jour = d + pd.Timedelta(days=365 * s + int(k * (95 if s == 4 else 290) / len(order[:n_played])))
                rows.append((jour, clubs[i], clubs[j], hg, ag))
        hist = pd.DataFrame(rows, columns=["date", "home", "away", "hg", "ag"]).sort_values("date")
        self.truth[div] = (hist.reset_index(drop=True), att, dfn)
        return self.truth[div]

    def _odds(self, probs, margin, noise):
        p = np.clip(np.asarray(probs) * np.exp(self.rng.normal(0, noise, len(probs))), 0.01, 0.99)
        p = p / p.sum() * (1 + margin)
        return [round(max(1.01, 1 / x), 2) for x in p]

    def _ev(self, ident, home, away, P, start):
        mk = markets(P)
        true3 = [mk["H"], mk["D"], mk["A"]]
        ev = {"id": ident, "home": self.ODDS_NAMES.get(home, home), "away": self.ODDS_NAMES.get(away, away),
              "start": start, "betclic": {"h2h": {}, "totals": {}}, "pinnacle": {"h2h": {}, "totals": {}}}
        ev["betclic"]["h2h"] = dict(zip("HDA", self._odds(true3, 0.065, 0.07)))
        ev["pinnacle"]["h2h"] = dict(zip("HDA", self._odds(true3, 0.025, 0.03)))
        m2 = markets(P, 2.5)                    # comme l'API : une seule ligne de buts (2,5) par bookmaker
        b = self._odds([m2["over"], m2["under"]], 0.06, 0.06)
        q = self._odds([m2["over"], m2["under"]], 0.025, 0.03)
        ev["betclic"]["totals"][2.5] = {"Over": b[0], "Under": b[1]}
        ev["pinnacle"]["totals"][2.5] = {"Over": q[0], "Under": q[1]}
        return ev

    def cotes(self, comp):
        if comp["id"] == "basketball_nba":
            return self._cotes_nba()
        if comp.get("ldc"):
            return self._cotes_ldc()
        div = comp.get("div")
        if div not in self.CLUBS:
            return []
        hist, att, dfn = self._league(div)
        clubs = self.CLUBS[div]
        idx = self.rng.permutation(len(clubs))
        evs = []
        for k in range(0, len(idx) - 1, 2):            # une journée complète
            i, j = int(idx[k]), int(idx[k + 1])
            P = score_grid(np.exp(0.22 + att[i] - dfn[j]), np.exp(att[j] - dfn[i]), -0.07)
            evs.append(self._ev(f"{div}-{k}", clubs[i], clubs[j], P,
                                self.now + timedelta(days=1 + (k % 6) / 3, hours=6)))
        return evs

    def _cotes_ldc(self):
        """Une soirée de Ligue des Champions (mardi) : 8 matchs entre clubs des 4 championnats."""
        pool = []
        for div in ("E0", "SP1", "D1", "F1"):
            _, att, dfn = self._league(div)
            pool += [(self.CLUBS[div][i], att[i] + 0.15, dfn[i] + 0.15) for i in range(6)]
        idx = self.rng.permutation(len(pool))[:16]
        mardi = (self.now + timedelta(days=(1 - self.now.weekday()) % 7)).replace(hour=17, minute=45)
        evs = []
        for k in range(0, 16, 2):
            (h, ah, dh), (a, aa, da) = pool[int(idx[k])], pool[int(idx[k + 1])]
            P = score_grid(np.exp(0.18 + ah - da), np.exp(aa - dh), -0.07)
            evs.append(self._ev(f"ldc-{k}", h, a, P, mardi + timedelta(hours=0 if k < 4 else 2, minutes=15 if k >= 4 else 0)))
        return evs

    def historique_foot(self, comp, now):
        div = comp.get("div")
        return self._league(div)[0] if div in self.CLUBS else None

    def _nba_truth(self):
        if "nba" not in self.truth:
            self.truth["nba"] = np.sort(self.rng.normal(0, 4.5, 30))[::-1] + self.rng.normal(0, 1, 30)
        return self.truth["nba"]

    def games_nba(self, now):
        s, rng, rows = self._nba_truth(), self.rng, []
        for season in (2024, 2025, 2026):
            n_games = 1230 if season < 2026 else 230
            start = pd.Timestamp(f"{season}-10-22")
            for g in range(n_games):
                i, j = rng.choice(30, 2, replace=False)
                diff = s[i] - s[j] + 2.5 + rng.normal(0, 12)
                tot = 228 + rng.normal(0, 18)
                rows.append((start + pd.Timedelta(days=int(g * (170 if season < 2026 else 28) / n_games)),
                             self.NBA[i], self.NBA[j], round(tot / 2 + diff / 2), round(tot / 2 - diff / 2), season))
        return pd.DataFrame(rows, columns=["date", "home", "away", "hpts", "apts", "season"])

    def _cotes_nba(self):
        from scipy.stats import norm as N
        s = self._nba_truth()
        idx = self.rng.permutation(30)
        evs = []
        for k in range(0, 16, 2):
            i, j = int(idx[k]), int(idx[k + 1])
            p = N.cdf((s[i] - s[j] + 2.5) / 12)
            ev = {"id": f"nba-{k}", "home": self.NBA[i], "away": self.NBA[j],
                  "start": self.now + timedelta(days=k / 5, hours=12),
                  "betclic": {"h2h": dict(zip("HA", self._odds([p, 1 - p], 0.055, 0.06))), "totals": {}},
                  "pinnacle": {"h2h": dict(zip("HA", self._odds([p, 1 - p], 0.022, 0.025))), "totals": {}}}
            line = float(round(228 + self.rng.normal(0, 6)) + 0.5)
            ev["betclic"]["totals"][line] = {"Over": 1.87, "Under": 1.87}
            ev["pinnacle"]["totals"][line] = {"Over": 1.95, "Under": 1.95}
            evs.append(ev)
        return evs

    def blessures_nba(self):
        return {self.NBA[3]: [{"joueur": "Joueur X (démo)", "statut": "Out"}],
                self.NBA[9]: [{"joueur": "Joueur Y (démo)", "statut": "Day-To-Day"}]}

    def joueurs(self, comp, now):
        div = comp.get("div")
        if div not in self.CLUBS:
            return None
        rows = []
        for c in self.CLUBS[div]:
            for r in range(4):
                g = int(self.rng.integers(6, 13))
                t = g * float(self.rng.uniform(55, 88))
                xg90 = [0.55, 0.32, 0.2, 0.12][r] * float(self.rng.uniform(0.7, 1.3))
                xg = xg90 * t / 90
                rows.append((f"Attaquant {r + 1} {c}", c, g, t, int(self.rng.poisson(xg)), xg))
        return pd.DataFrame(rows, columns=["joueur", "team", "games", "time", "goals", "xG"])

    def joueurs_nba(self, now):
        """Joueurs simulés : 8 par équipe, 12 matchs ; quelques-uns en forte hausse."""
        rng, rows = np.random.default_rng(5), []
        prenoms = ["Jalen", "Tyrese", "Marcus", "Darius", "Isaiah", "Keldon", "Jaden", "Malik"]
        for t, team in enumerate(self.NBA):
            for k in range(8):
                base_pts = [26, 19, 14, 11, 9, 7, 6, 5][k] * rng.uniform(0.8, 1.2)
                base_reb = [6, 8, 5, 4, 7, 3, 4, 2][k] * rng.uniform(0.8, 1.2)
                base_ast = [6, 3, 4, 2, 2, 3, 1, 1][k] * rng.uniform(0.8, 1.2)
                hausse = 1.6 if (t + k) % 23 == 4 else 1.25 if k == 0 and t % 5 == 0 else 1.0
                for j in range(12):
                    f = hausse if j >= 7 else 1.0
                    rows.append({"joueur": f"{prenoms[k]} {team.split()[-1]} (démo)", "equipe": team,
                                 "date": pd.Timestamp("2026-11-19") - pd.Timedelta(days=2 * (11 - j)),
                                 "min": [35, 32, 29, 26, 24, 22, 18, 14][k] * (1.15 if f > 1.3 else 1.0),
                                 "pts": max(0, rng.normal(base_pts * f, 4)), "reb": max(0, rng.normal(base_reb * f, 2)),
                                 "ast": max(0, rng.normal(base_ast * f, 1.5)), "poste": ["PG", "SF", "SG", "PF", "C", "G", "F", "C"][k]})
        return pd.DataFrame(rows).round({"pts": 0, "reb": 0, "ast": 0})

    def joueurs_foot(self, comp, now):
        div = comp.get("div")
        if div not in self.CLUBS:
            return None
        rng, rows = np.random.default_rng(len(div) * 7), []
        nats = ["France", "Espagne", "Angleterre", "Brésil", "Allemagne", "Portugal", "Argentine", "Maroc"]
        for i, club in enumerate(self.CLUBS[div]):
            for k, poste in enumerate(["Attaquant", "Attaquant", "Milieu", "Milieu"]):
                mj = int(rng.integers(8, 13))
                minutes = mj * rng.uniform(55, 88)
                g90 = [0.6, 0.35, 0.2, 0.12][k] * rng.uniform(0.6, 1.4) * (1.3 if i < 4 else 1.0)
                a90 = [0.15, 0.2, 0.25, 0.15][k] * rng.uniform(0.6, 1.4)
                rows.append({"joueur": f"Joueur {k + 1} {club} (démo)", "equipe": self.ODDS_NAMES.get(club, club),
                             "age": int(rng.integers(18, 33)), "nationalite": nats[(i + k) % len(nats)], "poste": poste,
                             "mj": mj, "minutes": minutes, "buts": round(g90 * minutes / 90), "passes": round(a90 * minutes / 90),
                             "note": 7.0, "forme": float(rng.uniform(2, 9)) if div == "E0" else 0.0,
                             "popularite": float(rng.uniform(1, 30)) if div == "E0" else None})
        return pd.DataFrame(rows)

    def actus(self, items, now):
        return {items[1]["id"]: {"alerte": True, "resume": "Démo : avant-centre titulaire incertain (cuisse)"}} \
            if len(items) > 1 else {}


# =============================================================================
# STATISTIQUES DESCRIPTIVES (affichées dans le rapport)
# =============================================================================
def season_start_foot(now) -> pd.Timestamp:
    return pd.Timestamp(year=now.year if now.month >= 7 else now.year - 1, month=7, day=15)


def stats_equipe_foot(hist, team, now, top6) -> dict:
    s = hist[(hist["date"] >= season_start_foot(now)) & ((hist["home"] == team) | (hist["away"] == team))]
    if s.empty:
        return {}
    dom = s["home"] == team
    gf = np.where(dom, s["hg"], s["ag"])
    ga = np.where(dom, s["ag"], s["hg"])
    res = np.where(gf > ga, "V", np.where(gf == ga, "N", "D"))
    opp = np.where(dom, s["away"], s["home"])
    vs_top = np.isin(opp, list(top6))
    n = len(s)
    v, nn, d = (res == "V").sum(), (res == "N").sum(), (res == "D").sum()
    vd = res[dom.to_numpy()]
    ve = res[~dom.to_numpy()]
    return {
        "MJ": n, "VND": f"{v}-{nn}-{d}", "pV": v / n,
        "pV_dom": (vd == "V").mean() if len(vd) else float("nan"),
        "pV_ext": (ve == "V").mean() if len(ve) else float("nan"),
        "BM": gf.mean(), "BE": ga.mean(),
        "O25": ((gf + ga) > 2.5).mean(), "BTTS": ((gf > 0) & (ga > 0)).mean(), "CS": (ga == 0).mean(),
        "forme": "".join(res[-5:]), "pts5": int(sum({"V": 3, "N": 1, "D": 0}[x] for x in res[-5:])),
        "BM_top6": gf[vs_top].mean() if vs_top.any() else float("nan"), "n_top6": int(vs_top.sum()),
    }


def stats_equipe_nba(games, team, now) -> dict:
    cur = games["season"].max()
    s = games[(games["season"] == cur) & ((games["home"] == team) | (games["away"] == team))]
    if s.empty:
        return {}
    dom = (s["home"] == team).to_numpy()
    pf = np.where(dom, s["hpts"], s["apts"])
    pa = np.where(dom, s["apts"], s["hpts"])
    res = np.where(pf > pa, "V", "D")
    last = s["date"].max()
    return {
        "MJ": len(s), "VD": f"{(res == 'V').sum()}-{(res == 'D').sum()}", "pV": (res == "V").mean(),
        "pV_dom": (res[dom] == "V").mean() if dom.any() else float("nan"),
        "pV_ext": (res[~dom] == "V").mean() if (~dom).any() else float("nan"),
        "PM": pf.mean(), "PE": pa.mean(), "net": (pf - pa).mean(),
        "forme": "".join(res[-5:]), "v10": int((res[-10:] == "V").sum()), "dernier": last,
    }


def badge_niveau(rang: int, n: int) -> str:
    if rang <= max(1, round(n / 3)):
        return "SOLIDE"
    if rang > n - round(n / 3):
        return "FAIBLE"
    return "MOYEN"


# =============================================================================
# PROBABILITÉS, EDGE, MISES
# =============================================================================
def devig_dict(d: dict, keys) -> dict | None:
    if not all(k in d for k in keys):
        return None
    try:
        return dict(zip(keys, devig_power([d[k] for k in keys])))
    except Exception:
        return None


def melanger(p_mod, p_mkt, cat):
    if p_mod is not None and p_mkt is not None:
        w = W_MODELE[cat]
        return w * p_mod + (1 - w) * p_mkt, "modèle + marché"
    if p_mkt is not None:
        return p_mkt, "marché seul"
    if p_mod is not None:
        return p_mod, "modèle seul"
    return None, "aucune"


def mise_kelly(p, cote) -> float:
    """Mise conseillée en % de bankroll : Kelly fractionné, plafonné."""
    b = cote - 1
    f = (p * b - (1 - p)) / b if b > 0 else 0
    return max(0.0, min(MISE_MAX_PCT, 100 * KELLY_FRACTION * f))


def option(match, marche, libelle, cote, p_mod, p_mkt, cat, groupe):
    p, source = melanger(p_mod, p_mkt, cat)
    if p is None or cote is None:
        return None
    edge = p * cote - 1
    seuil = EDGE_MIN * (2 if source == "modèle seul" else 1)
    if edge > EDGE_SUSPECT:
        statut = "SUSPECT"
    elif edge >= seuil and cote >= COTE_MIN:
        statut = "VALUE"
    else:
        statut = "NON"
    return {"match_id": match["id"], "match": f"{match['home']} – {match['away']}", "comp": match["comp"],
            "cat": cat, "start": match["start"], "marche": marche, "libelle": libelle, "groupe": groupe,
            "cote": cote, "p_mod": p_mod, "p_mkt": p_mkt, "p": p, "source": source, "edge": edge,
            "cote_min": 1 / p, "statut": statut, "mise": mise_kelly(p, cote) if statut == "VALUE" else 0.0,
            "alerte": match.get("alerte", "")}


# =============================================================================
# EFFECTIFS : API-Football (gratuit, 100 requêtes/jour) + Fantasy Premier League (Angleterre, sans clé)
# =============================================================================
API_FOOT_BASE = "https://v3.football.api-sports.io"
API_FOOT_MAX_JOUR = 95                       # marge sous la limite gratuite de 100 requêtes par jour
LIGUES_APIFOOT = {"soccer_epl": 39, "soccer_spain_la_liga": 140, "soccer_germany_bundesliga": 78,
                  "soccer_france_ligue_one": 61, "soccer_uefa_champs_league": 2}


def saison_foot(now) -> int:
    return now.year if now.month >= 7 else now.year - 1


class APIFoot:
    """Client API-Football : chaque réponse est mise en cache, chaque requête comptée (remise à zéro chaque jour)."""

    def __init__(self, echecs: list):
        self.ok = bool(API_FOOTBALL_KEY)
        self.echecs = echecs
        self.erreurs = set()
        self.f_compteur = CACHE_DIR / "apifoot_compteur.json"

    def _compteur(self, ajout=0) -> int:
        jour = datetime.now(TZ).strftime("%Y-%m-%d")
        try:
            d = json.loads(self.f_compteur.read_text())
        except Exception:
            d = {}
        if d.get("jour") != jour:
            d = {"jour": jour, "n": 0}
        if ajout:
            d["n"] += ajout
            CACHE_DIR.mkdir(exist_ok=True)
            self.f_compteur.write_text(json.dumps(d))
        return d["n"]

    def _erreur(self, msg):
        if msg not in self.erreurs:
            self.erreurs.add(msg)
            self.echecs.append(f"API-Football : {msg}")
            log(f"   API-Football : {msg}")

    def get(self, chemin, params, ttl_h, garder_vide=True):
        if not self.ok:
            return None
        cle = chemin.strip("/").replace("/", "_") + "_" + "_".join(f"{k}-{v}" for k, v in sorted(params.items()))
        f = CACHE_DIR / "apifoot" / (re.sub(r"[^A-Za-z0-9_.-]", "", cle) + ".json")
        if f.exists() and time.time() - f.stat().st_mtime < ttl_h * 3600:
            try:
                return json.loads(f.read_text(encoding="utf-8"))
            except Exception:
                pass
        if self._compteur() >= API_FOOT_MAX_JOUR:
            self._erreur("quota du jour atteint, données reprises au prochain lancement")
            return None
        r = http_get(API_FOOT_BASE + chemin, params=params, headers={"x-apisports-key": API_FOOTBALL_KEY},
                     timeout=20, retries=1)
        self._compteur(1)
        if r is None:
            self._erreur("pas de réponse (clé invalide ou service indisponible)")
            return None
        try:
            data = r.json()
        except ValueError:
            self._erreur("réponse illisible")
            return None
        if data.get("errors"):
            self._erreur(re.sub(r"\s+", " ", str(data["errors"]))[:200])
            return None
        rep = data.get("response", [])
        if rep or garder_vide:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rep), encoding="utf-8")
        return rep

    # --- appels utilisés ---
    def fixtures(self, ligue, jour, now):
        return self.get("/fixtures", {"league": ligue, "season": saison_foot(now), "date": jour}, ttl_h=12) or []

    def blessures(self, ligue, jour, now):
        return self.get("/injuries", {"league": ligue, "season": saison_foot(now), "date": jour}, ttl_h=4) or []

    def meilleurs_buteurs(self, ligue, now):
        return self.get("/players/topscorers", {"league": ligue, "season": saison_foot(now)}, ttl_h=24) or []

    def meilleurs_passeurs(self, ligue, now):
        return self.get("/players/topassists", {"league": ligue, "season": saison_foot(now)}, ttl_h=24) or []

    def compos(self, fixture_id):
        # une compo pas encore publiée n'est pas mise en cache : on redemande au prochain contrôle
        return self.get("/fixtures/lineups", {"fixture": fixture_id}, ttl_h=6, garder_vide=False) or []

    def trouver_match(self, ligue, home, away, start, now):
        """Le match API-Football correspondant (même date UTC, ou la veille / le lendemain)."""
        for decal in (0, -1, 1):
            jour = (start.astimezone(timezone.utc) + timedelta(days=decal)).strftime("%Y-%m-%d")
            for fx in self.fixtures(ligue, jour, now):
                eq = fx.get("teams") or {}
                h, a = (eq.get("home") or {}).get("name", ""), (eq.get("away") or {}).get("name", "")
                if match_team(home, [h]) and match_team(away, [a]):
                    return fx
        return None


def nom_affiche(nom) -> str:
    return str(nom).split(" / ")[0]


def meme_joueur(a, b) -> bool:
    """« E. Haaland », « Erling Haaland » et « Haaland » désignent le même joueur.
    Un nom peut porter une variante après « / » (« Rodrigo Hernández / Rodri »)."""
    if " / " in str(a) or " / " in str(b):
        return any(_meme_nom(x, y) for x in str(a).split(" / ") for y in str(b).split(" / "))
    return _meme_nom(a, b)


def _meme_nom(a, b) -> bool:
    na, nb = norm(a).split(), norm(b).split()
    if not na or not nb:
        return False
    if na == nb:
        return True
    if na[-1] == nb[-1]:
        if len(na) == 1 or len(nb) == 1:
            return True
        return na[0][0] == nb[0][0]
    longs_a = {t for t in na if len(t) >= 4}
    longs_b = {t for t in nb if len(t) >= 4}
    return bool(longs_a & longs_b) and (len(na) == 1 or len(nb) == 1)


def dans_liste(nom, noms) -> bool:
    return any(meme_joueur(nom, n) for n in noms)


def fpl_joueurs():
    """Joueurs de Premier League depuis l'API officielle du Fantasy (statut, chance de jouer, buts, xG, minutes)."""
    raw = cached_bytes("https://fantasy.premierleague.com/api/bootstrap-static/", "fpl_bootstrap.json",
                       max_age_h=6, headers=UA_NAV)
    if raw is None:
        return None
    try:
        d = json.loads(raw)
        equipes = {t["id"]: t["name"] for t in d["teams"]}
        rows = [{"joueur": f'{p["first_name"]} {p["second_name"]}', "court": p.get("web_name", ""),
                 "team": equipes.get(p["team"], ""), "statut": p.get("status", "a"),
                 "chance": p.get("chance_of_playing_next_round"), "news": p.get("news", ""),
                 "time": float(p.get("minutes") or 0), "games": float(p.get("starts") or 0),
                 "goals": float(p.get("goals_scored") or 0), "xG": float(p.get("expected_goals") or 0),
                 "passes": float(p.get("assists") or 0), "xA": float(p.get("expected_assists") or 0),
                 "forme": float(p.get("form") or 0), "popularite": float(p.get("selected_by_percent") or 0),
                 "poste": {1: "Gardien", 2: "Défenseur", 3: "Milieu", 4: "Attaquant"}.get(p.get("element_type"), "")}
                for p in d["elements"]]
        return pd.DataFrame(rows)
    except Exception as e:
        log(f"   Fantasy Premier League illisible : {e}")
        return None


def buteurs_apifoot(api, ligue, now):
    """Meilleurs buteurs API-Football au format des joueurs Understat (xG estimé : pas de xG dans le plan gratuit)."""
    rows = []
    for it in api.meilleurs_buteurs(ligue, now):
        try:
            st = it["statistics"][0]
            mj = float(st["games"].get("appearences") or 0)
            mins = float(st["games"].get("minutes") or 0)
            buts = float(st["goals"].get("total") or 0)
            tirs = float((st.get("shots") or {}).get("total") or 0)
            if mins <= 0:
                continue
            xg = 0.5 * buts + 0.5 * 0.11 * tirs if tirs else 0.85 * buts      # estimation prudente
            rows.append({"joueur": it["player"]["name"], "team": st["team"]["name"], "games": mj, "time": mins,
                         "goals": buts, "xG": xg, "titularisations": float(st["games"].get("lineups") or 0)})
        except Exception:
            continue
    return pd.DataFrame(rows) if rows else None


def joueurs_cles(team, joueurs_df, n=3):
    """Les n joueurs les plus décisifs d'une équipe (buts, puis xG)."""
    if joueurs_df is None or joueurs_df.empty:
        return []
    t = match_team(team, joueurs_df["team"].unique().tolist())
    if not t:
        return []
    j = joueurs_df[joueurs_df["team"] == t].sort_values(["goals", "xG"], ascending=False)
    j = j[(j["time"] >= 180) & ((j["goals"] >= 1) | (j["xG"] >= 1))]     # joue et pèse sur l'attaque
    if "court" in j.columns:                      # Fantasy : le nom court sert aussi (« Rodri », « Saka »)
        return [f"{r.joueur} / {r.court}" if r.court and norm(r.court) not in norm(r.joueur).split() else r.joueur
                for r in j.head(n).itertuples()]
    return j["joueur"].head(n).tolist()


def enrichir_effectifs(matchs_f, src, now):
    """Blessures et suspensions avant le bilan : alerte si un joueur clé manque, buteurs absents retirés."""
    api = getattr(src, "apifoot", None)
    fpl = src.fpl() if hasattr(src, "fpl") else None
    if (api is None or not api.ok) and fpl is None:
        return
    comp_par_nom = {c["nom"]: c for c in COMPETITIONS}
    for m in matchs_f:
        comp = comp_par_nom.get(m["comp"], {})
        ligue = LIGUES_APIFOOT.get(comp.get("id"))
        absents, douteux = [], []
        # 1) API-Football : blessures et suspensions du jour du match, pour la ligue
        if api is not None and api.ok and ligue:
            fx = api.trouver_match(ligue, m["home"], m["away"], m["start"], now)
            if fx:
                m["fixture_id"] = fx["fixture"]["id"]
                jour = fx["fixture"]["date"][:10]
                for b in api.blessures(ligue, jour, now):
                    if (b.get("fixture") or {}).get("id") != m["fixture_id"]:
                        continue
                    nom, eq = b["player"]["name"], b["team"]["name"]
                    cote = "home" if match_team(m["home"], [eq]) else "away"
                    raison = b["player"].get("reason") or ""
                    (absents if b["player"].get("type") == "Missing Fixture" else douteux).append(
                        {"nom": nom, "cote": cote, "raison": raison})
        # 2) Premier League : statut officiel Fantasy (blessé, suspendu, chance de jouer)
        if fpl is not None and comp.get("id") == "soccer_epl":
            for cote in ("home", "away"):
                t = match_team(m[cote], fpl["team"].unique().tolist())
                if not t:
                    continue
                for r in fpl[fpl["team"] == t].itertuples():
                    ch = None if pd.isna(r.chance) else int(r.chance)
                    nom = f"{r.joueur} / {r.court}" if r.court else r.joueur
                    if r.statut in ("i", "s", "u") or (ch is not None and ch <= 25):
                        if not dans_liste(nom, [x["nom"] for x in absents]):
                            absents.append({"nom": nom, "cote": cote, "raison": r.news})
                    elif r.statut == "d" or (ch is not None and ch <= 75):
                        if not dans_liste(nom, [x["nom"] for x in douteux]):
                            douteux.append({"nom": nom, "cote": cote, "raison": r.news})
        # 3) joueurs clés de chaque équipe
        sources_cles = []
        if api is not None and api.ok and ligue:           # d'abord API-Football : mêmes noms que les compos
            sources_cles.append(buteurs_apifoot(api, ligue, now))
        if fpl is not None and comp.get("id") == "soccer_epl":
            sources_cles.append(fpl)
        cles = {"home": [], "away": []}
        for cote in ("home", "away"):
            for df in sources_cles:
                for nom in joueurs_cles(m[cote], df):
                    if not dans_liste(nom, cles[cote]):
                        cles[cote].append(nom)
            for b in m["buteurs"]:                # les buteurs conseillés sont clés par définition
                if match_team(b["equipe"], [m[cote]]) and not dans_liste(b["joueur"], cles[cote]):
                    cles[cote].append(b["joueur"])
        m["cles"], m["absents"], m["douteux"] = cles, absents, douteux
        manquent = [f'{nom_affiche(x["nom"])} ({m[x["cote"]]})' for x in absents if dans_liste(x["nom"], cles[x["cote"]])]
        incertains = [f'{nom_affiche(x["nom"])} ({m[x["cote"]]})' for x in douteux if dans_liste(x["nom"], cles[x["cote"]])]
        if manquent:
            m["alerte"] = (m.get("alerte", "") + " · " if m.get("alerte") else "") + "Absent(s) clé(s) : " + ", ".join(manquent)
        if incertains:
            m["notes"].append("Incertain(s) : " + ", ".join(incertains))
        noms_absents = [x["nom"] for x in absents]
        m["buteurs"] = [b for b in m["buteurs"] if not dans_liste(b["joueur"], noms_absents)]
        for b in m["buteurs"]:
            if dans_liste(b["joueur"], [x["nom"] for x in douteux]):
                b["douteux"] = True


# =============================================================================
# PÉRIMÈTRE : quels matchs analyser
# =============================================================================
def classement_actuel(hist, now) -> list[str]:
    """Classement de la saison en cours (points, puis différence de buts, puis buts marqués)."""
    s = hist[hist["date"] >= season_start_foot(now)]
    if s.empty:
        return []
    pts, diff, bm = {}, {}, {}
    for r in s.itertuples():
        for eq, gf, ga in ((r.home, r.hg, r.ag), (r.away, r.ag, r.hg)):
            pts[eq] = pts.get(eq, 0) + (3 if gf > ga else 1 if gf == ga else 0)
            diff[eq] = diff.get(eq, 0) + gf - ga
            bm[eq] = bm.get(eq, 0) + gf
    return sorted(pts, key=lambda t: (-pts[t], -diff[t], -bm[t]))


def perimetre(comp, src, now):
    """Renvoie (clubs retenus en noms normalisés, texte lisible) ; None = tous les matchs."""
    if comp.get("ldc"):
        txt = "tous les matchs" + (" (sans les clubs italiens)" if EXCLURE_ITALIENS_LDC else "")
        return None, txt
    if not comp.get("equipes"):
        return None, "tous les matchs"
    retenus = list(comp["equipes"])
    ajouts = []
    if comp.get("top_n") or comp.get("plus_meilleurs"):
        hist = src.historique_foot(comp, now) if comp.get("div") else None
        ordre = classement_actuel(hist, now) if hist is not None else []
        connus = {canon(t) for t in retenus}
        if comp.get("top_n"):
            ajouts += [t for t in ordre[:comp["top_n"]] if canon(t) not in connus]
        if comp.get("plus_meilleurs"):
            ajouts += [t for t in ordre if canon(t) not in connus and t not in ajouts][:comp["plus_meilleurs"]]
        if not ordre:
            src.echecs.append(f"Classement {comp['nom']} indisponible : seuls les clubs fixes sont retenus")
    retenus += ajouts
    txt = ", ".join(retenus[:len(comp["equipes"])])
    if ajouts:
        txt += " + " + ", ".join(ajouts) + (" (4e actuel)" if comp.get("plus_meilleurs") and not comp.get("top_n")
                                             else " (top actuel)")
    return {canon(t) for t in retenus}, txt


def garder_match(ev, clubs) -> bool:
    if clubs is None:
        return True
    return canon(ev["home"]) in clubs or canon(ev["away"]) in clubs


def est_italien(nom) -> bool:
    return canon(nom) in {canon(c) for c in CLUBS_ITALIENS}


# =============================================================================
# ANALYSE FOOT
# =============================================================================
def analyser_foot(comp, events, src, now):
    hist = src.historique_foot(comp, now) if comp.get("div") else None
    model = None
    teams_hist = []
    rangs, top6 = {}, set()
    if hist is not None and len(hist) > 300:
        model = DixonColes().fit(hist, ref_date=pd.Timestamp(now.replace(tzinfo=None)))
        # niveau actuel = équipes ayant joué depuis 1 an
        recent = hist[hist["date"] >= pd.Timestamp(now.replace(tzinfo=None)) - pd.Timedelta(days=365)]
        teams_hist = sorted(set(recent["home"]) | set(recent["away"]))
        force = {t: model.att[model.teams.index(t)] + model.dfn[model.teams.index(t)] for t in teams_hist}
        ordre = sorted(force, key=force.get, reverse=True)
        rangs = {t: i + 1 for i, t in enumerate(ordre)}
        top6 = set(ordre[:6])
    joueurs = src.joueurs(comp, now) if model is not None else None

    out = []
    for ev in events:
        m = {"id": ev["id"], "home": ev["home"], "away": ev["away"], "start": ev["start"], "comp": comp["nom"],
             "cat": "FOOT", "options": [], "notes": [], "buteurs": []}
        h = match_team(ev["home"], teams_hist) if model else None
        a = match_team(ev["away"], teams_hist) if model else None
        P = None
        if model is not None and h and a:
            P, lam, mu = model.grid(h, a)
            m.update(lam=lam, mu=mu, h=h, a=a)
            m["stats_h"] = stats_equipe_foot(hist, h, now, top6) | {"rang": rangs[h], "badge": badge_niveau(rangs[h], len(rangs))}
            m["stats_a"] = stats_equipe_foot(hist, a, now, top6) | {"rang": rangs[a], "badge": badge_niveau(rangs[a], len(rangs))}
            m["n_equipes"] = len(rangs)
        elif model is not None:
            m["notes"].append(f"Équipe non reconnue dans l'historique ({ev['home'] if not h else ev['away']}) : "
                              "ajoute un alias dans ALIASES_RAW")
        else:
            m["notes"].append("Pas d'historique de championnat : probabilités = marché Pinnacle seul")
        out.append(m)

        bc, pn = ev["betclic"], ev["pinnacle"]
        mk = markets(P) if P is not None else None
        if P is not None:                     # probabilités du modèle sur plusieurs lignes de buts
            m["buts_mod"] = {l: (markets(P, l)["over"], markets(P, l)["under"]) for l in LIGNES_BUTS}
        fair = devig_dict(pn["h2h"], "HDA")
        noms = {"H": f"Victoire {ev['home']}", "D": "Match nul", "A": f"Victoire {ev['away']}"}
        for k in "HDA":
            o = option(m, "1N2", noms[k], bc["h2h"].get(k), mk[k] if mk else None,
                       fair[k] if fair else None, "FOOT", "1N2")
            if o:
                m["options"].append(o)
        for line, cotes in sorted(bc["totals"].items()):
            fair_t = devig_dict(pn["totals"].get(line, {}), ["Over", "Under"])
            mk_t = markets(P, line) if P is not None else None
            for side, cle in (("Over", "over"), ("Under", "under")):
                lib = f"{'Plus' if side == 'Over' else 'Moins'} de {line:g} buts".replace(".", ",")
                o = option(m, "Buts", lib, cotes.get(side), mk_t[cle] if mk_t else None,
                           fair_t[side] if fair_t else None, "FOOT", f"buts{line}")
                if o:
                    m["options"].append(o)
        if P is not None and fair is None:
            m["notes"].append("Pas de cote Pinnacle : probabilité = modèle seul (seuil de value doublé)")

        # ---- buteurs : P(marque) = 1 - exp(-λ joueur) ----
        if joueurs is not None and P is not None:
            for team_hist, lam_team, adv in ((h, m["lam"], a), (a, m["mu"], h)):
                noms_us = joueurs["team"].unique().tolist()
                t_us = match_team(team_hist, noms_us)
                if not t_us:
                    continue
                jt = joueurs[joueurs["team"] == t_us]
                mj_team = max(1, int(jt["games"].max()))
                xg_team_match = jt["xG"].sum() / mj_team
                if xg_team_match <= 0:
                    continue
                for r in jt.itertuples():
                    if r.games < 4 or r.time / r.games < 55:
                        continue
                    min_att = min(r.time / r.games, 90)
                    xg90 = r.xG / r.time * 90
                    lam_j = xg90 * (min_att / 90) * (lam_team / xg_team_match)
                    pj = 1 - math.exp(-lam_j)
                    if pj >= 0.25:
                        m["buteurs"].append({"joueur": r.joueur, "equipe": team_hist, "adv": adv,
                                             "p": pj, "cote_min": 1 / pj, "buts": int(r.goals),
                                             "xg90": xg90, "min": min_att, "mj": int(r.games),
                                             "match": f"{ev['home']} – {ev['away']}", "start": ev["start"],
                                             "comp": comp["nom"]})
            m["buteurs"].sort(key=lambda x: -x["p"])
            m["buteurs"] = m["buteurs"][:4]
    return out


# =============================================================================
# ANALYSE NBA
# =============================================================================
def elo_nba(games):
    elo, last_season, rest = NBAElo(), None, {}
    for g in games.sort_values("date").itertuples():
        if last_season is not None and g.season != last_season:
            elo.new_season()
        last_season = g.season
        elo.update(g.home, g.away, g.hpts, g.apts)
    return elo


def analyser_nba(comp, events, src, now, blessures):
    games = src.games_nba(now) if comp.get("nba") else None
    elo = elo_nba(games) if games is not None and len(games) > 500 else None
    teams = sorted(set(games["home"]) | set(games["away"])) if games is not None else []
    rangs = {}
    if elo:
        ordre = sorted(teams, key=elo.rating, reverse=True)
        rangs = {t: i + 1 for i, t in enumerate(ordre)}
    out = []
    for ev in events:
        m = {"id": ev["id"], "home": ev["home"], "away": ev["away"], "start": ev["start"], "comp": comp["nom"],
             "cat": "BASKET", "options": [], "notes": [], "buteurs": []}
        h = match_team(ev["home"], teams) if elo else None
        a = match_team(ev["away"], teams) if elo else None
        p_mod = None
        if elo and h and a:
            p_mod = elo.p_home(h, a)
            for cle, t in (("stats_h", h), ("stats_a", a)):
                st = stats_equipe_nba(games, t, now)
                if st:
                    repos = (pd.Timestamp(ev["start"].astimezone(TZ).date()) - st["dernier"]).days
                    st.update(rang=rangs[t], badge=badge_niveau(rangs[t], len(rangs)), elo=elo.rating(t),
                              repos=repos)
                m[cle] = st
            m["n_equipes"] = len(rangs)
            # back-to-back : le modèle Elo l'ignore, on le signale
            for cle, nom in (("stats_h", ev["home"]), ("stats_a", ev["away"])):
                if m.get(cle, {}).get("repos") == 1:
                    m["notes"].append(f"{nom} joue en back-to-back (2e match en 2 jours)")
        elif comp.get("nba"):
            m["notes"].append("Modèle Elo indisponible pour ce match : marché Pinnacle seul")
        else:
            m["notes"].append("Pas de modèle EuroLeague : probabilités = marché Pinnacle seul")
        # blessures (ESPN)
        bl = []
        for team_name, lst in blessures.items():
            if canon(team_name) in (canon(ev["home"]), canon(ev["away"])):
                bl += [f"{x['joueur']} ({x['statut']}, {team_name.split()[-1]})" for x in lst
                       if x["statut"].lower() in ("out", "doubtful", "questionable", "day-to-day")]
        if bl:
            m["blesses"] = bl
            if any("(Out" in b for b in bl):
                m["alerte"] = "Joueur(s) absent(s) : " + ", ".join(b for b in bl if "(Out" in b)[:160]
        out.append(m)

        bc, pn = ev["betclic"], ev["pinnacle"]
        fair = devig_dict(pn["h2h"], "HA")
        for k, lib, pm in (("H", f"Victoire {ev['home']}", p_mod), ("A", f"Victoire {ev['away']}",
                                                                   None if p_mod is None else 1 - p_mod)):
            o = option(m, "Vainqueur", lib, bc["h2h"].get(k), pm, fair[k] if fair else None, "BASKET", "1N2")
            if o:
                m["options"].append(o)
        for line, cotes in sorted(bc["totals"].items()):
            fair_t = devig_dict(pn["totals"].get(line, {}), ["Over", "Under"])
            for side in ("Over", "Under"):
                lib = f"{'Plus' if side == 'Over' else 'Moins'} de {line:g} pts".replace(".", ",")
                o = option(m, "Points", lib, cotes.get(side), None, fair_t[side] if fair_t else None,
                           "BASKET", f"pts{line}")
                if o:
                    m["options"].append(o)
    return out


# =============================================================================
# NOMBRE DE BUTS : conseil pour chaque match de foot
# =============================================================================
def conseils_buts(matchs_f):
    """Pour chaque match : les lignes +1,5 / +2,5 / +3,5 (chance, cote Betclic si proposée) et un conseil."""
    out = []
    for m in sorted(matchs_f, key=lambda x: x["start"]):
        opts = {o["libelle"]: o for o in m["options"] if o["marche"] == "Buts"}
        lignes = []
        for l in sorted(set(LIGNES_BUTS) | {float(re.sub(r"[^0-9,]", "", o["libelle"]).replace(",", "."))
                                           for o in opts.values()}):
            for sens, i in (("Plus", 0), ("Moins", 1)):
                lib = f"{sens} de {l:g} buts".replace(".", ",")
                o = opts.get(lib)
                p = o["p"] if o else (m.get("buts_mod", {}).get(l, (None, None))[i])
                if p is None:
                    continue
                lignes.append({"ligne": l, "sens": sens, "libelle": lib, "p": p, "opt": o,
                               "cote": o["cote"] if o else None, "cote_min": 1 / p})
        if not lignes:
            continue
        jouables = [x for x in lignes if x["opt"] and x["opt"]["cote"] >= COTE_MIN and not x["opt"]["alerte"]
                    and x["opt"]["statut"] != "SUSPECT"]
        value = [x for x in jouables if x["opt"]["statut"] == "VALUE"]
        if value:
            choix, raison = max(value, key=lambda x: x["opt"]["edge"]), "bonne cote"
        elif jouables:
            choix, raison = max(jouables, key=lambda x: x["p"]), "le plus probable (cote un peu basse)"
        else:                                  # aucune cote Betclic : la ligne la plus probable au-dessus de 1,5 buts
            sans = [x for x in lignes if x["p"] <= 0.85] or lignes
            choix, raison = max(sans, key=lambda x: x["p"]), "à vérifier sur Betclic"
        out.append({"match": m, "lignes": lignes, "choix": choix, "raison": raison})
    return out


# =============================================================================
# SÉLECTION : value bets, plus probables, combinés, outsiders
# =============================================================================
def selectionner(matchs):
    opts = [o for m in matchs for o in m["options"] if o["cote"] >= COTE_MIN]
    value = sorted([o for o in opts if o["statut"] == "VALUE"], key=lambda o: -o["edge"])
    probables, vus = [], set()
    for o in sorted([o for o in opts if o["p"] >= 0.60 and o["edge"] > -0.04], key=lambda o: -o["p"]):
        if o["match_id"] not in vus:          # une seule sélection par match, pour varier
            probables.append(o)
            vus.add(o["match_id"])
        if len(probables) == 8:
            break
    suspects = [o for o in opts if o["statut"] == "SUSPECT"]
    return value, probables, suspects


COMBI_EDGE_MIN = -0.06      # une sélection de combiné peut être un peu sous le juste prix (marge Betclic), pas plus
COTE_MAX_COMBI = 10.0       # aucun combiné au-dessus de cette cote totale
MAX_SELECTIONS = 6          # ni au-delà de ce nombre de sélections


def clubs_top():
    """Les meilleures équipes de la sélection : les clubs fixés dans COMPETITIONS (gros favoris européens)."""
    return {canon(t) for c in COMPETITIONS for t in c.get("equipes", [])}


def est_victoire_top(o, top) -> bool:
    return (o["marche"] == "1N2" and o["libelle"].startswith("Victoire ")
            and canon(o["libelle"][len("Victoire "):]) in top)


def _plafonne(legs, nom):
    """Garde les sélections les plus probables tant que la cote totale reste <= COTE_MAX_COMBI."""
    pris, cote = [], 1.0
    for o in sorted([l for l in legs if l], key=lambda o: -o["p"]):
        if len(pris) >= MAX_SELECTIONS:
            break
        if cote * o["cote"] <= COTE_MAX_COMBI:
            pris.append(o)
            cote *= o["cote"]
    return _combo(pris, nom) if len(pris) >= 2 else None


def _combo(legs, nom=""):
    legs = tuple(legs)
    cote = math.prod(o["cote"] for o in legs)
    p = math.prod(o["p"] for o in legs)
    return {"nom": nom, "legs": legs, "cote": cote, "p": p, "ev": p * cote - 1}


def _chercher(cands, kmin, kmax, cmin, cmax, n=2, critere=lambda c: -c["p"]):
    """Les n meilleurs combinés (une sélection par match), sans sélection en commun entre eux."""
    cands = sorted(cands, key=lambda o: -o["p"])[:14]
    cmax, kmax = min(cmax, COTE_MAX_COMBI), min(kmax, MAX_SELECTIONS)
    trouves = []
    for k in range(kmin, kmax + 1):
        for legs in itertools.combinations(cands, k):
            if len({o["match_id"] for o in legs}) < k:
                continue
            cote = math.prod(o["cote"] for o in legs)
            if cmin <= cote <= cmax:
                trouves.append(_combo(legs))
    trouves.sort(key=critere)
    retenus, deja = [], set()
    for c in trouves:
        ids = {(o["match_id"], o["libelle"]) for o in c["legs"]}
        if ids & deja:
            continue
        retenus.append(c)
        deja |= ids
        if len(retenus) == n:
            break
    return retenus


def _plus_probable(m, filtre=lambda o: True):
    ok = [o for o in m["options"] if o["cote"] >= COTE_MIN and o["statut"] != "SUSPECT" and not o["alerte"]
          and filtre(o)]
    return max(ok, key=lambda o: o["p"]) if ok else None


def construire_combines(matchs):
    """Paris Safe (2,00-2,50), Paris plus difficiles (~4,00), Combiné global, Spécial Ligue des Champions."""
    matchs = [m for m in matchs if m["cat"] == "FOOT"]          # combinés : foot uniquement
    pool = [o for m in matchs for o in m["options"]
            if o["cote"] >= COTE_MIN and o["statut"] != "SUSPECT" and not o["alerte"] and o["edge"] >= COMBI_EDGE_MIN]
    top = clubs_top()
    pool_fav = [o for m in matchs for o in m["options"]          # favoris : on tolère un peu plus de marge
                if o["cote"] >= COTE_MIN and o["statut"] != "SUSPECT" and not o["alerte"]
                and o["edge"] >= -0.10 and o["p"] >= 0.55 and est_victoire_top(o, top)]
    favoris = [{**c, "nom": "Gros favoris"} for c in _chercher(pool_fav, 2, 4, 2.00, 2.50)]
    if not favoris:                                             # pas assez de favoris pour atteindre 2,00
        favoris = [{**c, "nom": "Gros favoris (cote sous 2,00 : pas assez de gros matchs cette semaine)"}
                   for c in _chercher(pool_fav, 2, 4, 1.40, 2.50, n=1, critere=lambda c: -c["cote"])]
    res = {
        "safe": _chercher([o for o in pool if o["p"] >= 0.60], 2, 4, 2.00, 2.50),
        "favoris": favoris,
        "difficile": _chercher([o for o in pool if o["p"] >= 0.50], 3, 5, 3.60, 4.50,
                               critere=lambda c: (-c["p"], abs(c["cote"] - 4))),
        "global": None, "ldc": [],
    }
    foot = sorted([m for m in matchs if m["cat"] == "FOOT"], key=lambda m: m["start"])
    meilleurs = [l for l in (_plus_probable(m) for m in foot) if l]
    gros = _chercher(meilleurs, 3, MAX_SELECTIONS, 5.0, COTE_MAX_COMBI, n=1)
    if gros:
        res["global"] = {**gros[0], "nom": f"Le plus gros combiné ({len(gros[0]['legs'])} matchs, cote max 10)"}
    else:
        c = _plafonne(meilleurs, "")
        if c:
            res["global"] = {**c, "nom": f"Le plus gros combiné ({len(c['legs'])} matchs, cote max 10)"}

    soirees = {}
    for m in foot:
        if m["comp"] == "Ligue des Champions":
            soirees.setdefault(m["start"].astimezone(TZ).date(), []).append(m)
    for jour, ms in sorted(soirees.items()):
        if len(ms) < 2:
            continue
        props = []
        nuit = [o for m in ms for o in m["options"] if o in pool]
        sur = _chercher([o for o in nuit if o["p"] >= 0.55], 2, 3, 1.80, 2.60, n=1)
        if sur:
            props.append({**sur[0], "nom": "Le plus sûr de la soirée"})
        fav = _plafonne([_plus_probable(m, lambda o: o["marche"] == "1N2" and o["libelle"].startswith("Victoire")
                                        and o["p"] >= 0.55) for m in ms], "Les favoris de la soirée")
        if fav:
            props.append(fav)
        buts = _plafonne([_plus_probable(m, lambda o: o["marche"] == "Buts") for m in ms], "Les buts de la soirée")
        if buts:
            props.append(buts)
        obj4 = _chercher(nuit, 2, 4, 3.50, 4.60, n=1, critere=lambda c: (-c["p"], abs(c["cote"] - 4)))
        if obj4:
            props.append({**obj4[0], "nom": "Objectif cote 4"})
        maxi = _plafonne([_plus_probable(m) for m in ms], "")
        if maxi:
            props.append({**maxi, "nom": f"Le maximum de matchs de la soirée ({len(maxi['legs'])} sur {len(ms)}, cote max 10)"})
        vus, uniques = set(), []
        for c in props:                         # pas deux fois le même ticket
            cle = frozenset((o["match_id"], o["libelle"]) for o in c["legs"])
            if cle not in vus:
                vus.add(cle)
                uniques.append(c)
        res["ldc"].append({"jour": jour, "n": len(ms), "combos": uniques})
    return res


JOURS_FR = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]


def groupes_combines(comb):
    """Liste (titre, explication, combinés) commune à l'e-mail, au PDF et à la page."""
    g = [("Paris Safe", "Cote totale entre 2,00 et 2,50 : les sélections les plus probables.", comb["safe"]),
         ("Paris Safe : gros favoris", "Uniquement des victoires des meilleures équipes de la sélection "
          "(PSG, top anglais, Bayern, Leverkusen, Dortmund, Real, Barça, Atlético).", comb["favoris"]),
         ("Paris plus difficiles", "Davantage de sélections pour une cote totale autour de 4,00.", comb["difficile"])]
    if comb["global"]:
        g.append(("Combiné global", "Les sélections les plus probables de la semaine, en restant sous une cote "
                  "totale de 10.", [comb["global"]]))
    for s in comb["ldc"]:
        g.append((f"Spécial Ligue des Champions : {JOURS_FR[s['jour'].weekday()]} {s['jour']:%d/%m}",
                  f"{s['n']} matchs ce soir-là : plusieurs combinés possibles.", s["combos"]))
    return g


def outsiders(matchs):
    out = []
    for m in matchs:
        n = m.get("n_equipes", 0)
        for cle, nom, adv_cle in (("stats_h", m["home"], "stats_a"), ("stats_a", m["away"], "stats_h")):
            st = m.get(cle) or {}
            if not st or st["rang"] <= max(3, round(n / 3)):
                continue
            en_forme = st.get("pts5", 0) >= 10 if m["cat"] == "FOOT" else st.get("forme", "").count("V") >= 4
            if not en_forme:
                continue
            lib = f"Victoire {nom}"
            opt = next((o for o in m["options"] if o["libelle"] == lib), None)
            out.append({"equipe": nom, "comp": m["comp"], "match": f"{m['home']} – {m['away']}", "st": st,
                        "adv": (m.get(adv_cle) or {}), "opt": opt, "n": n})
    return sorted(out, key=lambda x: -(x["opt"]["edge"] if x["opt"] else -1))[:5]


def archiver(matchs, now):
    """Archive toutes les cotes vues : dans quelques mois, tu pourras mesurer ta CLV."""
    rows = [{"releve": now.isoformat(), "comp": o["comp"], "match": o["match"], "debut": o["start"].isoformat(),
             "marche": o["marche"], "selection": o["libelle"], "cote_betclic": o["cote"],
             "p_marche": o["p_mkt"], "p_modele": o["p_mod"], "p": round(o["p"], 4), "edge": round(o["edge"], 4),
             "statut": o["statut"]} for m in matchs for o in m["options"]]
    if not rows:
        return
    CACHE_DIR.mkdir(exist_ok=True)
    f = CACHE_DIR / "archive_cotes.csv"
    pd.DataFrame(rows).to_csv(f, mode="a", header=not f.exists(), index=False)


# =============================================================================
# RENDU HTML (compatible e-mail : styles en ligne, pas de JavaScript)
# =============================================================================
C = {"txt": "#1f2328", "mut": "#5f6b7a", "bord": "#e3e7ec", "fond": "#f5f7fa", "carte": "#ffffff",
     "vert": "#0f7b3f", "vert_f": "#e6f4ec", "rouge": "#b42318", "rouge_f": "#fdecea",
     "ambre": "#9a5b00", "ambre_f": "#fff4e0", "bleu": "#1a56db", "bleu_f": "#e8f0fe",
     "foot": "#14532d", "basket": "#9a3412"}
F = "font-family:-apple-system,'Segoe UI',Roboto,Arial,sans-serif;"


def e(x) -> str:
    return html.escape(str(x))


def pct(x, d=0):
    return "–" if x is None or (isinstance(x, float) and math.isnan(x)) else f"{100 * x:.{d}f} %"


def num(x, d=2):
    return "–" if x is None or (isinstance(x, float) and math.isnan(x)) else f"{x:.{d}f}"


def heure(dt):
    jours = ["lun.", "mar.", "mer.", "jeu.", "ven.", "sam.", "dim."]
    d = dt.astimezone(TZ)
    return f"{jours[d.weekday()]} {d:%d/%m %H:%M}"


def pill(texte, fg, bg):
    return (f'<span style="display:inline-block;padding:2px 8px;border-radius:10px;font-size:11px;'
            f'font-weight:700;color:{fg};background:{bg};white-space:nowrap">{e(texte)}</span>')


def badge_edge(o):
    if o["statut"] == "SUSPECT":
        return pill("à vérifier", C["ambre"], C["ambre_f"])
    if o["statut"] == "VALUE":
        return pill(f"+{100 * o['edge']:.1f} %", C["vert"], C["vert_f"])
    return f'<span style="color:{C["mut"]};font-size:12px">{100 * o["edge"]:+.1f} %</span>'


def badge_niv(b):
    return {"SOLIDE": pill("FORT", C["rouge"], C["rouge_f"]), "MOYEN": pill("MOYEN", C["ambre"], C["ambre_f"]),
            "FAIBLE": pill("FAIBLE", C["vert"], C["vert_f"])}.get(b, "")


def forme_html(s):
    col = {"V": C["vert"], "N": "#8a94a3", "D": C["rouge"]}
    return "".join(f'<span style="display:inline-block;width:16px;height:16px;line-height:16px;text-align:center;'
                   f'border-radius:3px;margin-right:2px;font-size:10px;font-weight:700;color:#fff;'
                   f'background:{col.get(c, "#999")}">{c}</span>' for c in s)


def barre(p, couleur=None):
    w = int(round(100 * max(0, min(1, p))))
    couleur = couleur or (C["vert"] if p >= 0.6 else C["bleu"] if p >= 0.4 else "#8a94a3")
    return (f'<div style="width:70px;height:6px;background:{C["bord"]};border-radius:3px;margin-top:3px">'
            f'<div style="width:{w}%;height:6px;background:{couleur};border-radius:3px"></div></div>')


TH = f'style="text-align:left;padding:8px 10px;font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:{C["mut"]};border-bottom:1px solid {C["bord"]};background:{C["fond"]}"'
TD = f'style="padding:8px 10px;border-bottom:1px solid {C["bord"]};font-size:13px;vertical-align:top"'


def table(entetes, lignes, vide="Rien à signaler cette semaine."):
    if not lignes:
        return f'<p style="color:{C["mut"]};font-size:13px;margin:6px 0 14px">{e(vide)}</p>'
    th = "".join(f"<th {TH}>{h}</th>" for h in entetes)
    trs = "".join("<tr>" + "".join(f"<td {TD}>{c}</td>" for c in l) + "</tr>" for l in lignes)
    return (f'<table role="presentation" cellspacing="0" cellpadding="0" style="width:100%;border-collapse:collapse;'
            f'background:{C["carte"]};border:1px solid {C["bord"]};border-radius:8px;margin:6px 0 18px">'
            f"<thead><tr>{th}</tr></thead><tbody>{trs}</tbody></table>")


def titre(t, sous=""):
    s = f'<div style="color:{C["mut"]};font-size:13px;margin-top:2px">{sous}</div>' if sous else ""
    return f'<h2 style="font-size:17px;margin:26px 0 4px;color:{C["txt"]}">{t}</h2>{s}'


def bandeau(t, couleur):
    return (f'<div style="background:{couleur};color:#fff;padding:12px 16px;border-radius:8px;'
            f'font-size:18px;font-weight:700;margin:34px 0 4px">{t}</div>')


def cellule_selection(o, avec_match=True):
    al = f'<div style="color:{C["rouge"]};font-size:11px;margin-top:2px">⚠ {e(o["alerte"])}</div>' if o["alerte"] else ""
    mt = (f'<div style="color:{C["mut"]};font-size:12px">{e(o["match"])} · {e(o["comp"])} · {heure(o["start"])}</div>'
          if avec_match else "")
    return f'<b>{e(o["libelle"])}</b>{mt}{al}'


def cellule_proba(o):
    detail = []
    if o["p_mod"] is not None:
        detail.append(f"modèle {pct(o['p_mod'])}")
    if o["p_mkt"] is not None:
        detail.append(f"marché {pct(o['p_mkt'])}")
    return f'<b>{pct(o["p"])}</b>{barre(o["p"])}<div style="color:{C["mut"]};font-size:11px;margin-top:3px">{" · ".join(detail)}</div>'


def mise_txt(o):
    if o["statut"] != "VALUE":
        return "–"
    t = f"{o['mise']:.1f} %"
    if BANKROLL:
        t += f'<div style="color:{C["mut"]};font-size:11px">{BANKROLL * o["mise"] / 100:.2f} €</div>'
    return t


def section_value(value):
    lignes = [[cellule_selection(o),
               f'<b style="font-size:15px">{o["cote"]:.2f}</b>'
               f'<div style="color:{C["mut"]};font-size:11px;white-space:nowrap">juste {o["cote_min"]:.2f}</div>',
               cellule_proba(o),
               f'{badge_edge(o)}<div style="font-size:12px;margin-top:4px;white-space:nowrap">mise {mise_txt(o)}</div>']
              for o in value[:12]]
    return table(["Sélection", "Cote", "Probabilité", "Edge · mise"], lignes,
                 "Aucune cote Betclic ne dépasse la probabilité estimée de plus de "
                 f"{100 * EDGE_MIN:.0f} % cette semaine. C'est fréquent : mieux vaut ne rien jouer que jouer sans value.")


def section_probables(probables):
    lignes = [[cellule_selection(o), f"{o['cote']:.2f}", cellule_proba(o), badge_edge(o)] for o in probables]
    return table(["Sélection", "Cote", "Probabilité", "Edge"], lignes)


def section_combines(comb):
    blocs = []
    for titre_g, expl, combos in groupes_combines(comb):
        cartes = []
        for c in combos:
            legs = "".join(f'<tr><td style="padding:4px 0;font-size:13px">{e(o["libelle"])}'
                           f'<span style="color:{C["mut"]};font-size:11px"> · {e(o["match"])} · {heure(o["start"])}</span></td>'
                           f'<td style="padding:4px 0;font-size:13px;text-align:right;white-space:nowrap">'
                           f'{o["cote"]:.2f} <span style="color:{C["mut"]}">({pct(o["p"])})</span></td></tr>'
                           for o in c["legs"])
            ev_col = C["vert"] if c["ev"] > 0 else C["rouge"]
            nom = f'<div style="font-weight:700;font-size:13px;margin-bottom:4px">{e(c["nom"])}</div>' if c.get("nom") else ""
            cartes.append(
                f'<div style="border:1px solid {C["bord"]};border-radius:8px;padding:12px 14px;margin:8px 0;background:{C["carte"]}">'
                f'{nom}<table role="presentation" style="width:100%;border-collapse:collapse">{legs}</table>'
                f'<div style="border-top:1px solid {C["bord"]};margin-top:6px;padding-top:8px;font-size:13px">'
                f'Cote totale <b style="font-size:16px">{c["cote"]:.2f}</b> &nbsp;·&nbsp; '
                f'chance de passer <b>{pct(c["p"])}</b> &nbsp;·&nbsp; '
                f'rentabilité <b style="color:{ev_col}">{100 * c["ev"]:+.1f} %</b></div></div>')
        corps = "".join(cartes) or f'<p style="color:{C["mut"]};font-size:13px">Aucune combinaison possible cette semaine.</p>'
        blocs.append(f'<h3 style="font-size:14px;margin:16px 0 0">{e(titre_g)}</h3>'
                     f'<div style="color:{C["mut"]};font-size:12px">{e(expl)}</div>{corps}')
    return "".join(blocs)


def section_buts_html(conseils):
    lignes = []
    for x in conseils:
        m, ch = x["match"], x["choix"]
        cases = " · ".join(f'{l["libelle"].replace(" buts", "").replace("Plus de ", "+").replace("Moins de ", "−")} : '
                           f'<b>{pct(l["p"])}</b>' + (f' ({l["cote"]:.2f})' if l["cote"] else "")
                           for l in x["lignes"] if l["sens"] == "Plus" or l["ligne"] == 3.5)
        cote = f'{ch["cote"]:.2f}' if ch["cote"] else f'cote mini {ch["cote_min"]:.2f}'
        lignes.append([f'<b>{e(m["home"])} – {e(m["away"])}</b><div style="color:{C["mut"]};font-size:12px">'
                       f'{e(m["comp"])} · {heure(m["start"])}</div>',
                       f'<b>{e(ch["libelle"])}</b> · {cote} · {pct(ch["p"])}'
                       f'<div style="color:{C["mut"]};font-size:11px">{e(x["raison"])}</div>',
                       f'<span style="font-size:12px">{cases}</span>'])
    return table(["Match", "Conseil buts", "Chance par ligne (cote Betclic)"], lignes, "Aucun match de foot retenu.")


def ligne_equipe_foot(st):
    if not st:
        return f'<span style="color:{C["mut"]}">stats indisponibles</span>'
    return (f'{badge_niv(st["badge"])} <span style="color:{C["mut"]};font-size:11px">{st["rang"]}e force</span><br>'
            f'{forme_html(st["forme"])}<div style="font-size:12px;margin-top:4px;line-height:1.5">'
            f'{st["MJ"]} MJ · {st["VND"]} · {pct(st["pV"])} V '
            f'<span style="color:{C["mut"]}">(dom {pct(st["pV_dom"])} / ext {pct(st["pV_ext"])})</span><br>'
            f'Buts {num(st["BM"], 1)} / {num(st["BE"], 1)} par match · vs top 6 : {num(st["BM_top6"], 1)} '
            f'<span style="color:{C["mut"]}">({st["n_top6"]} m.)</span><br>'
            f'+2,5 : {pct(st["O25"])} · LDEM : {pct(st["BTTS"])} · CS : {pct(st["CS"])}</div>')


def ligne_equipe_nba(st):
    if not st:
        return f'<span style="color:{C["mut"]}">stats indisponibles</span>'
    b2b = pill("B2B", C["rouge"], C["rouge_f"]) if st.get("repos") == 1 else ""
    return (f'{badge_niv(st["badge"])} <span style="color:{C["mut"]};font-size:11px">{st["rang"]}e Elo</span> {b2b}<br>'
            f'{forme_html(st["forme"])}<div style="font-size:12px;margin-top:4px;line-height:1.5">'
            f'{st["MJ"]} MJ · {st["VD"]} · {pct(st["pV"])} V '
            f'<span style="color:{C["mut"]}">(dom {pct(st["pV_dom"])} / ext {pct(st["pV_ext"])})</span><br>'
            f'Pts {num(st["PM"], 1)} / {num(st["PE"], 1)} · net {st["net"]:+.1f} · {st["v10"]}/10 derniers</div>')


def section_matchs(matchs):
    lignes = []
    for m in sorted(matchs, key=lambda x: x["start"]):
        f = ligne_equipe_foot if m["cat"] == "FOOT" else ligne_equipe_nba
        opts = sorted(m["options"], key=lambda o: o["groupe"])
        h2h = [o for o in opts if o["groupe"] == "1N2"]
        autres = sorted([o for o in opts if o["groupe"] != "1N2"], key=lambda o: -o["edge"])[:2]
        cotes = " ".join(
            f'<span style="display:inline-block;border:1px solid {C["bord"]};border-radius:6px;padding:4px 8px;'
            f'margin:3px 4px 0 0;font-size:12px;background:{C["vert_f"] if o["statut"] == "VALUE" else C["carte"]}">'
            f'{e(o["libelle"].replace("Victoire ", "V. "))} <b>{o["cote"]:.2f}</b> '
            f'<span style="color:{C["mut"]}">{pct(o["p"])}</span>'
            + (f' {badge_edge(o)}' if o["statut"] != "NON" else "") + "</span>"
            for o in h2h + autres)
        att = f' · buts attendus {m["lam"]:.2f} – {m["mu"]:.2f}' if m.get("lam") is not None else ""
        notes = "".join(f'<div style="color:{C["ambre"]};font-size:12px;margin-top:6px">• {e(n)}</div>' for n in m["notes"])
        if m.get("alerte"):
            notes += f'<div style="color:{C["rouge"]};font-size:12px;margin-top:6px">⚠ {e(m["alerte"])}</div>'
        elif m.get("blesses"):
            notes += f'<div style="color:{C["mut"]};font-size:12px;margin-top:6px">Incertains : {e(", ".join(m["blesses"])[:150])}</div>'
        col = (f'<td style="width:50%;vertical-align:top;padding:8px 8px 0 0">'
               f'<div style="font-size:11px;color:{C["mut"]};text-transform:uppercase;letter-spacing:.04em">{{}}</div>'
               f'<div style="font-weight:700;margin:2px 0 4px">{{}}</div>{{}}</td>')
        lignes.append(
            f'<div style="background:{C["carte"]};border:1px solid {C["bord"]};border-radius:8px;padding:12px 14px;margin:8px 0">'
            f'<div style="font-size:15px;font-weight:700">{e(m["home"])} <span style="color:{C["mut"]};font-weight:400">vs</span> {e(m["away"])}</div>'
            f'<div style="color:{C["mut"]};font-size:12px;margin-top:2px">{e(m["comp"])} · {heure(m["start"])}{att}</div>'
            f'<table role="presentation" style="width:100%;border-collapse:collapse;margin-top:4px"><tr>'
            + col.format("Domicile", e(m["home"]), f(m.get("stats_h")))
            + col.format("Extérieur", e(m["away"]), f(m.get("stats_a")))
            + f'</tr></table><div style="margin-top:8px">{cotes or "–"}</div>{notes}</div>')
    if not lignes:
        return f'<p style="color:{C["mut"]};font-size:13px">Aucun match dans la fenêtre.</p>'
    return "".join(lignes)


def section_buteurs(matchs):
    bs = sorted([b for m in matchs for b in m["buteurs"]], key=lambda b: -b["p"])[:12]
    lignes = [[f'<b>{e(b["joueur"])}</b><div style="color:{C["mut"]};font-size:12px">{e(b["equipe"])} vs {e(b["adv"])} · {heure(b["start"])}</div>',
               f'<b>{pct(b["p"])}</b>{barre(b["p"])}',
               f'<b>{b["cote_min"]:.2f}</b>',
               f'{b["buts"]} buts en {b["mj"]} MJ<div style="color:{C["mut"]};font-size:11px">xG/90 {b["xg90"]:.2f} · {b["min"]:.0f} min/m</div>']
              for b in bs]
    intro = (f'<div style="color:{C["mut"]};font-size:12px;margin:2px 0 4px">Les cotes buteurs Betclic ne sont pas '
             f"dans l'API gratuite. Joue seulement si la cote Betclic est <b>au-dessus de la cote minimale + 10 %</b> "
             f"(la probabilité suppose que le joueur est titulaire : vérifie la compo).</div>")
    return intro + table(["Joueur", "P(marque)", "Cote minimale", "Saison"], lignes,
                         "Pas de données buteurs (Understat) pour les matchs de la semaine.")


def section_outsiders(outs):
    lignes = []
    for x in outs:
        st, o = x["st"], x["opt"]
        ligne_st = (f'{forme_html(st["forme"])}<div style="font-size:12px;margin-top:3px">{st["rang"]}e/{x["n"]} · '
                    + (f'{pct(st["pV"])} V · +2,5 : {pct(st["O25"])} · LDEM : {pct(st["BTTS"])}' if "O25" in st
                       else f'{pct(st["pV"])} V · net {st["net"]:+.1f}') + "</div>")
        adv = x["adv"]
        lignes.append([f'<b>{e(x["equipe"])}</b><div style="color:{C["mut"]};font-size:12px">{e(x["comp"])} · {e(x["match"])}</div>',
                       ligne_st,
                       (badge_niv(adv["badge"]) + f' <span style="font-size:11px;color:{C["mut"]}">{adv["rang"]}e</span>') if adv else "–",
                       (f'{o["cote"]:.2f} ({pct(o["p"])}) {badge_edge(o)}' if o else "–")])
    return table(["Équipe", "Forme", "Adversaire", "Sa victoire"], lignes,
                 "Aucune équipe hors du premier tiers n'est en grande forme dans les matchs de la semaine.")


def resume_html(matchs_f, matchs_b, value, src, now, fin):
    n_value = len(value)
    meilleur = max(value, key=lambda o: o["edge"]) if value else None
    stat = lambda v, l: (f'<td style="padding:10px 12px;background:{C["carte"]};border:1px solid {C["bord"]};border-radius:8px;text-align:center">'
                         f'<div style="font-size:22px;font-weight:800">{v}</div><div style="font-size:11px;color:{C["mut"]}">{l}</div></td>')
    cartes = (f'<table role="presentation" cellspacing="6" style="width:100%;border-collapse:separate;margin:10px 0 0"><tr>'
              + stat(len(matchs_f), "matchs foot") + stat(len(matchs_b), "matchs basket")
              + stat(n_value, "sélections value") + stat(e(src.quota), "crédits API restants") + "</tr></table>")
    phrase = (f"Meilleure value : <b>{e(meilleur['libelle'])}</b> à <b>{meilleur['cote']:.2f}</b> "
              f"({e(meilleur['match'])}), edge {100 * meilleur['edge']:+.1f} %." if meilleur
              else "Aucune value nette cette semaine : le rapport liste quand même les sélections les plus probables.")
    return (f'<div style="color:{C["mut"]};font-size:13px">Du {now.astimezone(TZ):%d/%m %H:%M} au {fin.astimezone(TZ):%d/%m %H:%M}</div>'
            f'{cartes}<p style="font-size:14px;margin:12px 2px 0">{phrase}</p>')


def lecture_html():
    return (f'<div style="background:{C["bleu_f"]};border-radius:8px;padding:12px 16px;font-size:12px;line-height:1.6;margin-top:16px">'
            f'<b>Comment lire ce rapport</b><br>'
            f'<b>Probabilité estimée</b> : {100 * W_MODELE["FOOT"]:.0f} % modèle Dixon-Coles (foot) ou '
            f'{100 * W_MODELE["BASKET"]:.0f} % Elo (NBA), le reste = cote Pinnacle sans marge (le marché le plus fiable).<br>'
            f'<b>Cote juste</b> = 1 / probabilité. En dessous, le pari perd de l\'argent à long terme.<br>'
            f'<b>Edge</b> = probabilité × cote Betclic − 1. {pill(f"+{100 * EDGE_MIN:.0f} %", C["vert"], C["vert_f"])} = value retenue. '
            f'{pill("à vérifier", C["ambre"], C["ambre_f"])} = edge > {100 * EDGE_SUSPECT:.0f} %, souvent une erreur (blessure, compo) plutôt qu\'une aubaine.<br>'
            f'<b>Mise</b> = Kelly ¼ plafonné à {MISE_MAX_PCT:g} % de la bankroll. '
            f'<b>Niveau</b> : SOLIDE / MOYEN / FAIBLE = tiers du classement de force du modèle. '
            f'<b>LDEM</b> = les deux équipes marquent · <b>CS</b> = clean sheet · <b>B2B</b> = back-to-back.</div>')


def generer_html(matchs_f, matchs_b, src, now, fin):
    tous = matchs_f + matchs_b
    value, probables, suspects = selectionner(tous)
    comb = construire_combines(tous)
    erreurs = "".join(f"<li>{e(x)}</li>" for x in dict.fromkeys(src.echecs))
    corps = (
        f'<div style="font-size:22px;font-weight:800">Bilan Betclic de la semaine</div>'
        + resume_html(matchs_f, matchs_b, value, src, now, fin)
        + lecture_html()
        + titre("① Sélections avec value", "La cote Betclic est au-dessus de la probabilité estimée. C'est la seule liste à jouer en simple.")
        + section_value(value)
        + titre("Nombre de buts : match par match", "Chance de chaque ligne d'après le modèle et le marché ; cote Betclic quand elle est proposée.")
        + section_buts_html(conseils_buts(matchs_f))
        + titre("② Combinés", "Une sélection maximum par match. La chance de passer = produit des probabilités.")
        + section_combines(comb)
        + titre("③ Les plus probables", "Pour réduire le risque. Edge négatif = la cote est trop basse pour être rentable à long terme.")
        + section_probables(probables)
        + bandeau("⚽ Football européen", C["foot"])
        + titre("Buteurs", "P(marque) = 1 − e<sup>−λ</sup>, λ = xG/90 du joueur × minutes × faiblesse de l'adversaire")
        + section_buteurs(matchs_f)
        + titre("Équipes moins en vue en forme", "Hors du premier tiers, au moins 10 points sur 5 matchs")
        + section_outsiders(outsiders(matchs_f))
        + titre("Tous les matchs")
        + section_matchs(matchs_f)
        + bandeau("🏀 Basket — NBA & EuroLeague", C["basket"])
        + titre("Équipes moins en vue en forme", "Hors du premier tiers Elo, au moins 4 victoires sur 5")
        + section_outsiders(outsiders(matchs_b))
        + titre("Tous les matchs")
        + section_matchs(matchs_b)
        + (titre("Données manquantes ou dégradées") + f'<ul style="font-size:12px;color:{C["mut"]}">{erreurs}</ul>' if erreurs else "")
        + f'<p style="font-size:11px;color:{C["mut"]};margin-top:28px;line-height:1.6">Aucun modèle ne garantit un gain : '
          f"même avec un edge réel, les séries perdantes sont normales. Ne mise que ce que tu peux perdre. "
          f"Joueurs Info Service : 09 74 75 13 13 (appel non surtaxé). Rapport généré le {datetime.now(TZ):%d/%m/%Y %H:%M}.</p>"
    )
    return (f'<!doctype html><html lang="fr"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1"><title>Bilan Betclic</title></head>'
            f'<body style="margin:0;background:{C["fond"]};{F}color:{C["txt"]}">'
            f'<div style="max-width:980px;margin:0 auto;padding:20px 14px">{corps}</div></body></html>'), value


# =============================================================================
# VOCABULAIRE SIMPLE (utilisé par l'e-mail et le PDF)
# =============================================================================
def fr(x, d=2) -> str:
    """Nombre à la française : 2,22."""
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return "–"
    return f"{x:.{d}f}".replace(".", ",")


def pc(x) -> str:
    """Pourcentage arrondi : 51 %."""
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return "–"
    if 0 < x < 0.01:
        return "moins de 1 %"
    return f"{round(100 * x)} %"


def verdict(p):
    """Niveau de risque en mots, d'après la chance de gagner."""
    if p >= 0.70:
        return "Très probable", "#0f7b3f", "#e6f4ec"
    if p >= 0.55:
        return "Probable", "#0f7b3f", "#e6f4ec"
    if p >= 0.40:
        return "Équilibré", "#1a56db", "#e8f0fe"
    if p >= 0.25:
        return "Risqué", "#9a5b00", "#fff4e0"
    return "Très risqué", "#b42318", "#fdecea"


def phrase_avantage(o) -> str:
    return (f"La cote Betclic ({fr(o['cote'])}) est plus haute que nécessaire : "
            f"il suffisait de {fr(o['cote_min'])} pour que ce pari soit rentable.")


def mise_mots(o) -> str:
    if o["statut"] != "VALUE" or o["mise"] <= 0:
        return ""
    t = f"Mise conseillée : {fr(o['mise'], 1)} % de ton capital"
    if BANKROLL:
        t += f" ({fr(BANKROLL * o['mise'] / 100)} €)"
    return t


def synthese(matchs_f, matchs_b):
    tous = matchs_f + matchs_b
    value, probables, suspects = selectionner(tous)
    a_jouer = sorted([o for o in value if not o["alerte"]], key=lambda o: -o["p"])
    buteurs = sorted([b for m in matchs_f for b in m["buteurs"]], key=lambda b: -b["p"])
    return {"value": value, "a_jouer": a_jouer, "probables": probables, "suspects": suspects,
            "comb": construire_combines(tous), "buteurs": buteurs, "buts": conseils_buts(matchs_f),
            "out_f": outsiders(matchs_f), "out_b": outsiders(matchs_b)}


# =============================================================================
# E-MAIL : court, gros caractères, lisible sur téléphone
# =============================================================================
def generer_email(matchs_f, matchs_b, syn, src, now, fin, avec_pdf: bool, page: bool = False) -> str:
    """page=True : version « appli » publiée sur le web (liens au lieu de pièce jointe)."""
    vert, gris, bord, txt = "#0f7b3f", "#5f6b7a", "#e3e7ec", "#1f2328"
    police = "font-family:-apple-system,'Segoe UI',Roboto,Arial,sans-serif;"

    def etiquette(t, fg, bg):
        return (f'<span style="display:inline-block;padding:3px 10px;border-radius:12px;font-size:14px;'
                f'font-weight:700;color:{fg};background:{bg}">{e(t)}</span>')

    def chiffre(valeur, legende, couleur=txt):
        return (f'<td style="padding:6px 4px;text-align:center;width:33%">'
                f'<div style="font-size:24px;font-weight:800;color:{couleur}">{valeur}</div>'
                f'<div style="font-size:13px;color:{gris}">{legende}</div></td>')

    def carte_pari(o, n):
        v, fg, bg = verdict(o["p"])
        mise = mise_mots(o)
        al = (f'<div style="margin-top:10px;font-size:14px;color:#b42318">Attention : {e(o["alerte"])}</div>'
              if o["alerte"] else "")
        return (f'<div style="border:1px solid {bord};border-radius:12px;padding:16px;margin:12px 0;background:#fff">'
                f'<div style="font-size:13px;color:{gris}">PARI {n}</div>'
                f'<div style="font-size:20px;font-weight:800;margin:4px 0 2px">{e(o["libelle"])}</div>'
                f'<div style="font-size:15px;color:{gris}">{e(o["match"])}<br>{e(o["comp"])} · {heure(o["start"])}</div>'
                f'<table role="presentation" style="width:100%;border-collapse:collapse;margin-top:12px;'
                f'border-top:1px solid {bord}"><tr>'
                + chiffre(fr(o["cote"]), "cote Betclic")
                + chiffre(pc(o["p"]), "chance de gagner")
                + chiffre(f"+{round(100 * o['edge'])} %", "avantage", vert)
                + f'</tr></table><div style="margin-top:8px">{etiquette(v, fg, bg)}</div>'
                f'<div style="font-size:14px;color:{gris};margin-top:8px;line-height:1.5">{e(phrase_avantage(o))}</div>'
                + (f'<div style="font-size:15px;font-weight:700;margin-top:8px">{e(mise)}</div>' if mise else "")
                + al + "</div>")

    def carte_combine(c, titre_c):
        if len(c["legs"]) > 6:              # long combiné : une ligne par sélection
            legs = "".join(
                f'<tr><td style="padding:3px 0;font-size:13px;border-bottom:1px solid {bord}">'
                f'<b>{e(o["libelle"])}</b> <span style="color:{gris}">· {e(o["match"])}</span></td>'
                f'<td style="padding:3px 0;font-size:13px;text-align:right;font-weight:700;border-bottom:1px solid {bord}">'
                f'{fr(o["cote"])}</td></tr>' for o in c["legs"])
        else:
            legs = "".join(
                f'<tr><td style="padding:6px 0;font-size:15px;border-bottom:1px solid {bord}">'
                f'<b>{e(o["libelle"])}</b><br><span style="color:{gris};font-size:13px">{e(o["match"])} · {heure(o["start"])}</span></td>'
                f'<td style="padding:6px 0;font-size:16px;text-align:right;font-weight:700;border-bottom:1px solid {bord}">{fr(o["cote"])}</td></tr>'
                for o in c["legs"])
        avert = ("" if c["ev"] > 0 else
                 f'<div style="font-size:13px;color:#9a5b00;margin-top:8px">Rentabilité négative : la marge de Betclic '
                 f'pèse plus que l\'avantage des sélections. Pari plaisir, pas un placement.</div>')
        return (f'<div style="border:1px solid {bord};border-radius:12px;padding:16px;margin:12px 0;background:#fff">'
                f'<div style="font-size:18px;font-weight:800;margin-bottom:6px">{e(titre_c)}</div>'
                f'<table role="presentation" style="width:100%;border-collapse:collapse">{legs}</table>'
                f'<table role="presentation" style="width:100%;border-collapse:collapse;margin-top:8px"><tr>'
                + chiffre(fr(c["cote"]), "cote totale")
                + chiffre(pc(c["p"]), "chance de passer")
                + chiffre(f"{round(100 * c['ev']):+d} %", "rentabilité", vert if c["ev"] > 0 else "#b42318")
                + f"</tr></table>{avert}</div>")

    def ligne_buts(x, derniere):
        m, ch = x["match"], x["choix"]
        autres = " · ".join(f'{l["libelle"].replace(" buts", "").replace("Plus de ", "+").replace("Moins de ", "−")} '
                            f'{pc(l["p"])}' for l in x["lignes"] if l["sens"] == "Plus" or l["ligne"] == 3.5)
        cote = fr(ch["cote"]) if ch["cote"] else f'mini {fr(ch["cote_min"] * 1.05)}'
        couleur = vert if x["raison"] == "bonne cote" else txt
        sep = "" if derniere else f"border-bottom:1px solid {bord};"
        return (f'<div style="padding:10px 0;{sep}">'
                f'<div style="font-size:13px;color:{gris}">{e(m["home"])} – {e(m["away"])} · {heure(m["start"])}</div>'
                f'<div style="font-size:16px;margin-top:2px"><b style="color:{couleur}">{e(ch["libelle"])}</b> · '
                f'<b>{cote}</b> · {pc(ch["p"])}</div>'
                f'<div style="font-size:12px;color:{gris};margin-top:2px">{autres}</div></div>')

    def titre_sec(t, sous=""):
        s = f'<div style="font-size:15px;color:{gris};margin-top:2px">{sous}</div>' if sous else ""
        return f'<div style="font-size:22px;font-weight:800;margin:30px 0 4px">{t}</div>{s}'

    n_matchs = len(matchs_f) + len(matchs_b)
    a_jouer = syn["a_jouer"][:5]
    if a_jouer:
        intro = (f"Sur <b>{n_matchs} matchs</b> analysés, <b>{len(syn['a_jouer'])} pari(s)</b> ont une cote Betclic "
                 f"plus haute que leur vraie chance de passer. Voici les {len(a_jouer)} plus sûrs.")
        bloc_paris = "".join(carte_pari(o, i + 1) for i, o in enumerate(a_jouer))
    else:
        intro = (f"Sur <b>{n_matchs} matchs</b> analysés, <b>aucune cote Betclic n'est assez haute</b> pour être "
                 f"rentable cette semaine. C'est normal certaines semaines : le mieux est de ne rien jouer.")
        bloc_paris = ""

    blocs_comb = ""
    for titre_g, expl, combos in groupes_combines(syn["comb"]):
        if not combos:
            continue
        blocs_comb += (f'<div style="font-size:18px;font-weight:800;margin:22px 0 0">{e(titre_g)}</div>'
                       f'<div style="font-size:14px;color:{gris}">{e(expl)}</div>')
        for c in combos[:2] if not titre_g.startswith("Spécial") else combos:
            blocs_comb += carte_combine(c, c.get("nom") or titre_g)
    bloc_buts_mail = ""
    if syn["buts"]:
        bloc_buts_mail = (f'<div style="border:1px solid {bord};border-radius:12px;padding:4px 16px;margin:12px 0;background:#fff">'
                          + "".join(ligne_buts(x, i == len(syn["buts"]) - 1) for i, x in enumerate(syn["buts"]))
                          + f'</div><div style="font-size:13px;color:{gris}">En vert : la cote Betclic est meilleure que '
                            f'la vraie chance. « mini » = pas de cote Betclic reçue, joue seulement au-dessus.</div>')

    buteurs = syn["buteurs"][:3]
    bloc_but = "".join(
        f'<div style="border:1px solid {bord};border-radius:12px;padding:14px 16px;margin:10px 0;background:#fff">'
        f'<div style="font-size:18px;font-weight:800">{e(b["joueur"])}'
        + (' <span style="font-size:13px;color:#9a5b00">(incertain)</span>' if b.get("douteux") else "") + '</div>'
        f'<div style="font-size:14px;color:{gris}">{e(b["equipe"])} contre {e(b["adv"])} · {heure(b["start"])}</div>'
        f'<div style="font-size:16px;margin-top:8px">Chance de marquer : <b>{pc(b["p"])}</b></div>'
        f'<div style="font-size:15px;margin-top:4px">Joue-le seulement si Betclic le cote <b>au moins {fr(b["cote_min"] * 1.1)}</b></div></div>'
        for b in buteurs)

    if page:
        return page_onglets(locals())
    pdf_txt = ("Tout le détail (stats de chaque équipe, tous les matchs, autres buteurs) est dans le "
               "<b>PDF joint</b> à ce mail." if avec_pdf else "")
    corps = (
        ("<!--COMPOS-->" if page else "")
        + f'<div style="font-size:28px;font-weight:800;line-height:1.2">Tes paris de la semaine</div>'
        f'<div style="font-size:15px;color:{gris};margin-top:4px">Matchs du {now.astimezone(TZ):%d/%m} au {fin.astimezone(TZ):%d/%m}</div>'
        f'<div style="font-size:17px;line-height:1.5;margin-top:16px">{intro}</div>'
        + (titre_sec("Les paris à jouer", "Un pari = une mise séparée.") + bloc_paris if bloc_paris else "")
        + (titre_sec("Nombre de buts : match par match", "Notre conseil pour chaque match, et la chance de chaque ligne (+1,5, +2,5, +3,5).") + bloc_buts_mail if bloc_buts_mail else "")
        + (titre_sec("Les combinés", "Plusieurs paris sur le même ticket : tous doivent passer. Une sélection par match.") + blocs_comb if blocs_comb else "")
        + (titre_sec("Buteurs à surveiller", "La cote buteur n'est pas connue à l'avance : vérifie-la sur Betclic et la compo.") + bloc_but if bloc_but else "")
        + (f'<div style="font-size:16px;background:#e8f0fe;border-radius:12px;padding:14px 16px;margin-top:28px;line-height:1.5">{pdf_txt}</div>' if pdf_txt else "")
        + f'<div style="font-size:13px;color:{gris};margin-top:24px;line-height:1.6">'
          f"Ces chiffres sont des estimations : même un bon pari perd souvent. Ne mise que ce que tu peux perdre. "
          f"Besoin d'aide : Joueurs Info Service, 09 74 75 13 13.</div>"
    )
    return (f'<!doctype html><html lang="fr"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1"><title>Mes paris</title>'
            f'<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes">'
            f'<meta name="apple-mobile-web-app-title" content="Mes paris"><meta name="theme-color" content="#14532d">'
            + ('<link rel="apple-touch-icon" href="apple-touch-icon.png"><link rel="icon" href="icon.png">'
               '<link rel="manifest" href="manifest.json">' if page else "") + '</head>'
            f'<body style="margin:0;background:#f5f7fa;{police}color:{txt}">'
            f'<div style="max-width:600px;margin:0 auto;padding:20px 14px">{corps}</div></body></html>')


# =============================================================================
# JOUEURS EN FORME ET PÉPITES (onglet « Joueurs » de l'appli)
# =============================================================================
STATS_NBA = (("pts", "points", 10), ("reb", "rebonds", 5), ("ast", "passes décisives", 4))


def lire_feuille_espn(box, jour):
    """Une feuille de match ESPN -> une ligne par joueur ayant joué (minutes, points, rebonds, passes)."""
    rows = []
    for eq in (box or {}).get("players", []):
        nom_eq = (eq.get("team") or {}).get("displayName", "")
        for bloc in eq.get("statistics", []):
            noms = [str(x).upper() for x in (bloc.get("names") or bloc.get("labels") or [])]
            if not all(k in noms for k in ("MIN", "PTS", "REB", "AST")):
                continue
            i = {k: noms.index(k) for k in ("MIN", "PTS", "REB", "AST")}
            for a in bloc.get("athletes", []):
                st = a.get("stats") or []
                if a.get("didNotPlay") or len(st) < len(noms):
                    continue
                try:
                    val = {k: float(str(st[j]).split(":")[0]) for k, j in i.items()}
                except ValueError:
                    continue
                ath = a.get("athlete") or {}
                rows.append({"joueur": ath.get("displayName", ""), "equipe": nom_eq,
                             "date": pd.to_datetime(str(jour), format="%Y%m%d"), "min": val["MIN"], "pts": val["PTS"],
                             "reb": val["REB"], "ast": val["AST"],
                             "poste": (ath.get("position") or {}).get("abbreviation", "")})
    return rows


def prochain_match(equipe, matchs):
    for m in sorted(matchs, key=lambda x: x["start"]):
        for cote, autre in (("home", "away"), ("away", "home")):
            if canon(m[cote]) == canon(equipe) or match_team(equipe, [m[cote]]):
                return m, m[autre]
    return None, None


def seuil_fiable(valeurs, mini_taux=0.7):
    """La ligne x,5 la plus haute franchie au moins 7 fois sur 10 sur les derniers matchs."""
    v = [float(x) for x in valeurs]
    if len(v) < 5:
        return None
    for ligne in np.arange(math.floor(max(v)) + 0.5, -0.5, -1.0):
        n = sum(x > ligne for x in v)
        if n / len(v) >= mini_taux:
            return {"ligne": float(ligne), "n": n, "sur": len(v), "taux": n / len(v)}
    return None


POSTES_NBA = {"G": "meneur ou arrière", "PG": "meneur", "SG": "arrière", "F": "ailier", "SF": "ailier",
              "PF": "ailier fort", "C": "pivot", "G-F": "arrière ou ailier", "F-C": "ailier fort ou pivot"}


def joueurs_nba_forme(df, matchs_b, n_forme=4):
    """Joueurs NBA en grande forme (points + rebonds + passes sur 5 matchs) et une pépite (joueur de rôle en hausse)."""
    nba = [m for m in matchs_b if m["comp"] == "NBA"]
    if df is None or df.empty or not nba:
        return None
    equipes = {canon(m[c]) for m in nba for c in ("home", "away")}
    cands = []
    for (nom, eq), g in df.sort_values("date").groupby(["joueur", "equipe"]):
        if canon(eq) not in equipes and not any(match_team(eq, [m[c]]) for m in nba for c in ("home", "away")):
            continue
        if len(g) < 6:
            continue
        d5, d10 = g.tail(5), g.tail(10)
        if d5["min"].mean() < 20:
            continue
        pra5 = d5[["pts", "reb", "ast"]].sum(axis=1).mean()
        pra_s = g[["pts", "reb", "ast"]].sum(axis=1).mean()
        m, adv = prochain_match(eq, nba)
        if m is None:
            continue
        paris = []
        for col, nom_stat, seuil_min in STATS_NBA:
            if d10[col].mean() < seuil_min:
                continue
            sf = seuil_fiable(d10[col].tolist())
            if sf and sf["ligne"] >= seuil_min - 0.5:
                paris.append({"stat": nom_stat, **sf})
        cands.append({"joueur": nom, "equipe": eq, "poste": POSTES_NBA.get(str(g["poste"].iloc[-1]), ""),
                      "n_matchs": len(g), "match": m, "adversaire": adv,
                      "r5": {k: d5[k].mean() for k in ("pts", "reb", "ast", "min")},
                      "rs": {k: g[k].mean() for k in ("pts", "reb", "ast", "min")},
                      "pra5": pra5, "ratio": pra5 / pra_s if pra_s else 1, "paris": paris})
    if not cands:
        return None
    forme = sorted([c for c in cands if c["pra5"] >= 25 and c["ratio"] >= 1.0],
                   key=lambda c: -c["pra5"] * min(c["ratio"], 1.4))[:n_forme]
    deja = {c["joueur"] for c in forme}
    pepites = sorted([c for c in cands if c["rs"]["pts"] < 15 and c["ratio"] >= 1.2 and c["r5"]["min"] >= 22
                      and c["joueur"] not in deja and c["paris"]], key=lambda c: -c["ratio"])
    return {"forme": forme, "pepite": pepites[0] if pepites else None}


def joueurs_foot_forme(dfs, matchs_f, n_forme=4):
    """Joueurs de foot en forme (buts + passes par 90 min, forme récente en Angleterre) et une pépite (jeune ou peu attendu)."""
    cands = []
    for comp_nom, df in dfs.items():
        if df is None or df.empty:
            continue
        ms = [m for m in matchs_f if m["comp"] == comp_nom]
        for r in df.itertuples():
            if r.minutes < 450 or r.buts + r.passes < 2:
                continue
            m, adv = prochain_match(r.equipe, ms)
            if m is None:
                continue
            g90, a90 = r.buts * 90 / r.minutes, r.passes * 90 / r.minutes
            mj = max(1.0, float(getattr(r, "mj", 0) or 0))
            min_match = min(90.0, r.minutes / mj)
            p_but = 1 - math.exp(-g90 * 0.85 * min_match / 90)
            p_passe = 1 - math.exp(-a90 * 0.85 * min_match / 90)
            forme_fpl = float(getattr(r, "forme", 0) or 0)
            cands.append({"joueur": r.joueur, "equipe": r.equipe, "comp": comp_nom, "match": m, "adversaire": adv,
                          "age": getattr(r, "age", None), "nationalite": getattr(r, "nationalite", "") or "",
                          "poste": getattr(r, "poste", "") or "", "buts": int(r.buts), "passes": int(r.passes),
                          "minutes": int(r.minutes), "mj": int(mj), "g90": g90, "a90": a90, "forme_fpl": forme_fpl,
                          "popularite": getattr(r, "popularite", None), "p_but": p_but, "p_passe": p_passe,
                          "score": (g90 + a90) * (1 + forme_fpl / 10)})
    if not cands:
        return None
    forme = sorted(cands, key=lambda c: -c["score"])[:n_forme]
    deja = {c["joueur"] for c in forme}
    reste = [c for c in cands if c["joueur"] not in deja]
    jeunes = [c for c in reste if c["age"] and not pd.isna(c["age"]) and int(c["age"]) <= 21 and c["g90"] + c["a90"] >= 0.3]
    peu_vus = [c for c in reste if c["popularite"] is not None and not pd.isna(c["popularite"])
               and c["popularite"] < 5 and c["forme_fpl"] >= 5]
    pepite = (max(jeunes, key=lambda c: c["score"]) if jeunes else max(peu_vus, key=lambda c: c["score"]) if peu_vus
              else (min(reste, key=lambda c: c["minutes"]) if reste else None))
    return {"forme": forme, "pepite": pepite}


def joueurs_semaine(src, matchs_f, matchs_b, now):
    """Données de l'onglet Joueurs : NBA et foot. Ne bloque jamais le bilan."""
    out = {"nba": None, "foot": None}
    try:
        if any(m["comp"] == "NBA" for m in matchs_b) and hasattr(src, "joueurs_nba"):
            out["nba"] = joueurs_nba_forme(src.joueurs_nba(now), matchs_b)
    except Exception as ex:
        log(f"   Joueurs NBA indisponibles ({ex})")
    try:
        if hasattr(src, "joueurs_foot"):
            dfs = {}
            for c in COMPETITIONS:
                if c["cat"] == "FOOT" and any(m["comp"] == c["nom"] for m in matchs_f):
                    dfs[c["nom"]] = src.joueurs_foot(c, now)
            out["foot"] = joueurs_foot_forme(dfs, matchs_f)
    except Exception as ex:
        log(f"   Joueurs foot indisponibles ({ex})")
    return out


# ---- présentation (faits uniquement : poste, âge, nationalité, chiffres) ----
def phrase_nba(c, pepite=False) -> str:
    r5, rs = c["r5"], c["rs"]
    qui = (f'{c["joueur"]}, {c["poste"]} des {c["equipe"]},' if c["poste"] else f'{c["joueur"]} ({c["equipe"]})')
    tendance = (f'contre {fr(rs["pts"], 1)} points en moyenne sur ses {c["n_matchs"]} matchs relevés'
                if abs(r5["pts"] - rs["pts"]) >= 0.5 else "au niveau de sa moyenne")
    debut = (f'{qui} monte en puissance : ' if pepite else f'{qui} tourne à ')
    return (f'{debut}{fr(r5["pts"], 1)} points, {fr(r5["reb"], 1)} rebonds et {fr(r5["ast"], 1)} passes sur ses '
            f'5 derniers matchs, en {fr(r5["min"], 0)} minutes, {tendance}.')


NATIONALITES = {"France": "Français", "Spain": "Espagnol", "England": "Anglais", "Germany": "Allemand",
                "Brazil": "Brésilien", "Argentina": "Argentin", "Portugal": "Portugais", "Netherlands": "Néerlandais",
                "Belgium": "Belge", "Italy": "Italien", "Norway": "Norvégien", "Morocco": "Marocain",
                "Senegal": "Sénégalais", "Ivory Coast": "Ivoirien", "Côte d'Ivoire": "Ivoirien", "Algeria": "Algérien",
                "Uruguay": "Uruguayen", "Colombia": "Colombien", "Croatia": "Croate", "Denmark": "Danois",
                "Sweden": "Suédois", "Poland": "Polonais", "Switzerland": "Suisse", "Austria": "Autrichien",
                "Scotland": "Écossais", "Wales": "Gallois", "Nigeria": "Nigérian", "Ghana": "Ghanéen",
                "Cameroon": "Camerounais", "Egypt": "Égyptien", "Japan": "Japonais", "South Korea": "Sud-Coréen",
                "USA": "Américain", "United States": "Américain", "Georgia": "Géorgien", "Turkey": "Turc",
                "Serbia": "Serbe", "Ukraine": "Ukrainien", "Ecuador": "Équatorien", "Mexico": "Mexicain"}


def phrase_foot(c) -> str:
    bits = [c["joueur"]]
    if c["age"] and not pd.isna(c["age"]):
        bits.append(f'{int(c["age"])} ans')
    if c["nationalite"]:
        bits.append(NATIONALITES.get(c["nationalite"], c["nationalite"]))
    qui = ", ".join(bits)
    role = f'{c["poste"].lower()} de {c["equipe"]}' if c["poste"] else f'joueur de {c["equipe"]}'
    par_but = f', soit un but toutes les {round(c["minutes"] / c["buts"])} minutes' if c["buts"] else ""
    forme = f' Sa note de forme Fantasy est de {fr(c["forme_fpl"], 1)}.' if c["forme_fpl"] else ""
    pl = lambda n, mot: f"{n} {mot}" + ("s" if n > 1 else "")
    return (f'{qui}, {role} : {pl(c["buts"], "but")} et {pl(c["passes"], "passe")} '
            f'décisive{"s" if c["passes"] > 1 else ""} en {c["mj"]} matchs cette saison'
            f'{par_but}.{forme}')


# =============================================================================
# L'APPLI « MES PARIS » (page de l'icône) : onglets, camemberts, ticket récapitulatif
# =============================================================================
MOIS_FR = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août", "septembre", "octobre",
           "novembre", "décembre"]
JOURS_COURTS = ["lun.", "mar.", "mer.", "jeu.", "ven.", "sam.", "dim."]

APPLI_CSS = """
:root{--rouge:#C1121F;--rouge-pale:#FDECEC;--encre:#18181B;--ardoise:#52525B;--gris:#A1A1AA;--clair:#D4D4D8;
--trait:#E4E4E7;--fond:#F7F7F8;--blanc:#FFFFFF;
--cond:'Barlow Semi Condensed','Arial Narrow',system-ui,sans-serif;--texte:'Barlow',system-ui,-apple-system,'Segoe UI',sans-serif}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--fond);color:var(--encre);font-family:var(--texte);font-size:16px;line-height:1.45}
.page{max-width:600px;margin:0 auto;padding:0 16px}
.tete{padding-top:22px;padding-bottom:14px}
.maj{color:var(--gris);font-size:13px;margin-top:2px}
.marque{display:flex;align-items:center;gap:10px}
.marque i{width:14px;height:14px;background:var(--rouge);border-radius:3px}
.marque h1{font:700 32px/1 var(--cond);letter-spacing:-.01em;margin:0}
.semaine{color:var(--ardoise);font-size:15px;margin-top:6px}
.onglets{position:sticky;top:0;z-index:10;background:var(--blanc);border-bottom:1px solid var(--trait)}
.rail{max-width:600px;margin:0 auto;display:flex;overflow-x:auto;scrollbar-width:none;padding:0 6px}
.rail::-webkit-scrollbar{display:none}
.onglet{flex:0 0 auto;background:none;border:0;border-bottom:3px solid transparent;padding:15px 10px 12px;
font:600 17px/1 var(--cond);color:var(--ardoise);cursor:pointer;white-space:nowrap}
.onglet[aria-selected=true]{color:var(--encre);border-bottom-color:var(--rouge)}
.onglet span{color:var(--gris);font-weight:500;margin-left:5px}
[data-panneau]{padding:6px 0 130px}
h2{font:700 23px/1.15 var(--cond);margin:24px 0 4px}
.aide{color:var(--ardoise);font-size:14px;margin:0 0 12px}
.intro{font-size:17px;margin:14px 0 4px}
.liste{background:var(--blanc);border:1px solid var(--trait);border-radius:12px;overflow:hidden}
.ligne{display:flex;align-items:center;gap:12px;padding:14px;border-top:1px solid var(--trait)}
.ligne:first-child{border-top:0}
.corps{flex:1;min-width:0}
.carte{display:grid;grid-template-columns:1fr auto;column-gap:12px;row-gap:2px;padding:14px;border-top:1px solid var(--trait)}
.carte:first-child{border-top:0}
.carte .droite{text-align:right}
.carte .bas{grid-column:1 / -1;display:flex;align-items:center;gap:10px;margin-top:8px}
.carte .bas .txt{flex:1;min-width:0;font-size:14px;color:var(--ardoise)}
.carte .bas .txt b{color:var(--encre);font-weight:600}
.carte .bas .txt .r{color:var(--rouge);font-weight:600}
.sel{font-weight:600;font-size:17px;line-height:1.25}
.qui{color:var(--ardoise);font-size:14px;margin-top:2px}
.prix{text-align:right;flex:0 0 auto}
.cote{font:700 27px/1 var(--cond)}
.mini{color:var(--ardoise);font-size:12px;white-space:nowrap;margin-top:3px}
.plus{font-size:14px;color:var(--rouge);font-weight:600;margin-top:4px}
.note{font-size:13px;color:var(--ardoise);margin-top:3px}
.alerte{font-size:13px;color:var(--rouge);margin-top:4px}
.pick{flex:0 0 auto;width:42px;height:42px;border-radius:50%;border:2px solid var(--clair);background:var(--blanc);
display:grid;place-items:center;cursor:pointer;color:var(--clair);padding:0}
.pick svg{width:18px;height:18px}
.pick[aria-pressed=true]{background:var(--rouge);border-color:var(--rouge);color:#fff}
button:focus-visible,a:focus-visible{outline:3px solid var(--rouge);outline-offset:2px}
.donut text{font:700 15px var(--cond);fill:var(--encre)}
.ticket{background:var(--blanc);border:1px solid var(--trait);border-radius:12px;margin:12px 0;overflow:hidden}
.ticket .haut{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:12px 14px;border-bottom:1px dashed var(--clair)}
.ticket .nom{font:700 18px/1.2 var(--cond)}
.jambe{display:flex;justify-content:space-between;gap:10px;padding:9px 14px;border-top:1px solid var(--trait)}
.jambe:first-of-type{border-top:0}
.jambe .c{font:700 19px/1.2 var(--cond)}
.ticket .bas{display:flex;align-items:center;gap:14px;padding:12px 14px;background:var(--fond);border-top:1px dashed var(--clair)}
.ticket .total{font:700 30px/1 var(--cond)}
.ticket .bas .quoi{flex:1;font-size:13px;color:var(--ardoise)}
.renta{font-size:13px;color:var(--ardoise)}
.renta.ok{color:var(--encre);font-weight:600}
.fiche{background:var(--blanc);border:1px solid var(--trait);border-radius:12px;padding:14px;margin:12px 0}
.fiche .titre{font:700 20px/1.2 var(--cond)}
.equipes{display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-top:12px}
.equipe .n{font-weight:600}
.niveau{font-size:13px;color:var(--ardoise)}
.niveau.fort{color:var(--rouge);font-weight:600}
.camembert{display:flex;align-items:center;gap:8px;margin:8px 0}
.legende{font-size:12px;color:var(--ardoise);line-height:1.5}
.forme b{display:inline-block;width:17px;height:17px;border-radius:4px;margin-right:2px;font:700 11px/17px var(--texte);text-align:center;color:#fff}
.forme .V{background:var(--rouge)}.forme .N{background:var(--gris)}.forme .D{background:var(--clair);color:var(--encre)}
.stat{font-size:13px;color:var(--ardoise);margin-top:3px}
.stat b{color:var(--encre);font-weight:600}
.puces{margin-top:12px}
.puce{border:1px solid var(--trait);background:var(--blanc);border-radius:999px;padding:7px 12px;font:500 14px var(--texte);
color:var(--encre);margin:6px 6px 0 0;cursor:pointer}
.puce b{font:700 16px var(--cond);margin-left:4px}
.puce.bon{border-color:var(--rouge)}
.puce[aria-pressed=true]{background:var(--rouge);border-color:var(--rouge);color:#fff}
.barres{margin-top:8px}
.barre{display:flex;align-items:center;gap:8px;font-size:13px;color:var(--ardoise);margin-top:4px}
.barre .l{width:44px}
.barre .p{flex:1;height:6px;background:var(--trait);border-radius:3px;overflow:hidden}
.barre .p i{display:block;height:100%;background:var(--gris)}
.barre.choix .p i{background:var(--rouge)}
.barre .v{width:38px;text-align:right;color:var(--encre)}
.vide{color:var(--ardoise);font-size:16px;margin:28px 0}
.joueur{background:var(--blanc);border:1px solid var(--trait);border-radius:12px;margin:12px 0;overflow:hidden}
.joueur.pepite{border-left:4px solid var(--rouge)}
.joueur .tete-j{display:flex;gap:12px;align-items:center;padding:14px 14px 0}
.avatar{flex:0 0 auto;width:44px;height:44px;border-radius:50%;background:var(--encre);color:#fff;display:grid;place-items:center;
font:700 17px var(--cond)}
.pepite .avatar{background:var(--rouge)}
.joueur .bio{padding:10px 14px 0;font-size:14px;color:var(--ardoise)}
.duo{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;padding:12px 14px}
.duo>div{background:var(--fond);border-radius:8px;padding:8px 6px;text-align:center}
.duo .v{font:700 22px/1 var(--cond)}
.duo .l{font-size:12px;color:var(--ardoise);margin-top:3px}
.duo .avant{font-size:12px;color:var(--ardoise)}
.duo .haut{color:var(--rouge)}
.sugg{display:flex;align-items:center;gap:10px;padding:10px 14px;border-top:1px solid var(--trait)}
.sugg .corps .sel{font-size:16px}
.etiquette{font:600 15px var(--cond);color:var(--rouge);margin:0 0 2px}
.liens{margin:28px 0 0;display:flex;gap:18px;flex-wrap:wrap}
.liens a{color:var(--rouge);font-weight:600;text-decoration:none}
.pied{color:var(--ardoise);font-size:13px;margin:26px 0 0}
.barre-ticket{position:fixed;left:0;right:0;bottom:0;z-index:20;background:var(--rouge);color:#fff;
padding:12px 16px calc(12px + env(safe-area-inset-bottom));transform:translateY(110%);transition:transform .25s ease}
.barre-ticket.visible{transform:none}
.barre-ticket .in{max-width:600px;margin:0 auto;display:flex;align-items:center;gap:14px}
.barre-ticket .n{font-size:15px;flex:1}
.barre-ticket .t{font:700 30px/1 var(--cond)}
.barre-ticket button{background:#fff;color:var(--rouge);border:0;border-radius:999px;padding:11px 16px;font:700 16px var(--cond);cursor:pointer}
.voile{position:fixed;inset:0;background:rgba(24,24,27,.45);z-index:30;opacity:0;pointer-events:none;transition:opacity .2s}
.voile.ouvert{opacity:1;pointer-events:auto}
.feuille{position:fixed;left:0;right:0;bottom:0;z-index:31;background:var(--blanc);border-radius:18px 18px 0 0;
max-height:86vh;overflow:auto;transform:translateY(105%);transition:transform .25s ease;
padding:8px 16px calc(18px + env(safe-area-inset-bottom))}
.feuille.ouvert{transform:none}
.feuille .in{max-width:600px;margin:0 auto}
.poignee{width:44px;height:5px;border-radius:3px;background:var(--clair);margin:6px auto 10px}
.feuille h2{margin-top:6px}
.retire{background:none;border:0;color:var(--ardoise);font-size:22px;line-height:1;padding:6px 8px;cursor:pointer}
.recap{margin:14px 0;padding:14px;border:1px dashed var(--clair);border-radius:12px}
.recap .t{font:700 34px/1 var(--cond);color:var(--rouge)}
.avert{color:var(--rouge);font-size:14px;margin-top:8px}
.actions{display:flex;gap:10px;flex-wrap:wrap;margin-top:14px}
.btn{border-radius:999px;padding:12px 18px;font:700 17px var(--cond);cursor:pointer;text-decoration:none;display:inline-block}
.btn.plein{background:var(--rouge);color:#fff;border:0}
.btn.creux{background:var(--blanc);color:var(--rouge);border:2px solid var(--rouge)}
.btn.texte{background:none;border:0;color:var(--ardoise)}
.info{position:fixed;left:50%;bottom:96px;transform:translateX(-50%);background:var(--encre);color:#fff;
padding:10px 16px;border-radius:999px;font-size:15px;z-index:40;opacity:0;transition:opacity .2s;pointer-events:none}
.info.visible{opacity:1}
@media (prefers-reduced-motion:reduce){.barre-ticket,.feuille,.voile,.info{transition:none}}
"""

APPLI_JS = r"""
(function(){
var ID=document.body.getAttribute('data-semaine'),CLE='mesparis-ticket-'+ID,memoire=[];
function lire(){try{var s=localStorage.getItem(CLE);return s?JSON.parse(s):memoire.slice();}catch(e){return memoire.slice();}}
function ecrire(t){memoire=t.slice();try{localStorage.setItem(CLE,JSON.stringify(t));}catch(e){}}
function fr(x){return (Math.round(x*100)/100).toFixed(2).replace('.',',');}
function pc(x){return x>0&&x<0.01?'moins de 1 %':Math.round(x*100)+' %';}
function esc(s){return String(s).replace(/[&<>"]/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c];});}
/* onglets */
var tabs=document.querySelectorAll('[data-onglet]'),pans=document.querySelectorAll('[data-panneau]');
function montre(id){pans.forEach(function(x){x.hidden=x.getAttribute('data-panneau')!==id;});
tabs.forEach(function(x){var on=x.getAttribute('data-onglet')===id;x.setAttribute('aria-selected',on?'true':'false');
x.tabIndex=on?0:-1;if(on&&x.scrollIntoView){x.scrollIntoView({block:'nearest',inline:'center'});}});
try{history.replaceState(null,'','#'+id);}catch(e){}}
tabs.forEach(function(x,i){x.addEventListener('click',function(){montre(x.getAttribute('data-onglet'));window.scrollTo(0,0);});
x.addEventListener('keydown',function(ev){var d=ev.key==='ArrowRight'?1:ev.key==='ArrowLeft'?-1:0;if(!d)return;
var n=tabs[(i+d+tabs.length)%tabs.length];n.focus();n.click();});});
function depuisAdresse(){var h=(location.hash||'').slice(1);montre(document.querySelector('[data-panneau="'+h+'"]')?h:'jouer');}
window.addEventListener('hashchange',depuisAdresse);depuisAdresse();
/* ticket */
var barre=document.getElementById('barre-ticket'),feuille=document.getElementById('feuille'),voile=document.getElementById('voile'),
contenu=document.getElementById('contenu-ticket'),info=document.getElementById('info');
function message(t){info.textContent=t;info.classList.add('visible');setTimeout(function(){info.classList.remove('visible');},1800);}
function total(t){var simples=t.filter(function(x){return x.cote&&!x.legs;});if(simples.length<2||simples.length!==t.length)return null;
var mids={},double=false;simples.forEach(function(x){(x.mids||[x.mid]).forEach(function(m){if(mids[m])double=true;mids[m]=1;});});
var c=1,p=1;simples.forEach(function(x){c*=x.cote;p*=x.p||0;});return {cote:c,p:p,double:double};}
function rafraichir(){var t=lire(),ids={};t.forEach(function(x){ids[x.id]=1;});
document.querySelectorAll('[data-item]').forEach(function(b){var it=JSON.parse(b.getAttribute('data-item'));
var on=!!ids[it.id];b.setAttribute('aria-pressed',on?'true':'false');
if(b.classList.contains('pick'))b.setAttribute('aria-label',(on?'Retirer du ticket : ':'Ajouter au ticket : ')+it.sel);});
var tot=total(t);barre.classList.toggle('visible',t.length>0);barre.setAttribute('aria-hidden',t.length?'false':'true');
document.getElementById('nb-ticket').textContent=t.length+(t.length>1?' sélections':' sélection');
document.getElementById('cote-ticket').textContent=tot?fr(tot.cote):'';
if(!t.length){contenu.innerHTML='<p class="vide">Ton ticket est vide. Coche des paris dans les onglets pour les retrouver ici.</p>';return;}
var h='<div class="liste">';t.forEach(function(x){h+='<div class="ligne"><div class="corps"><div class="sel">'+esc(x.sel)+'</div><div class="qui">'+esc(x.match)+(x.quand?', '+esc(x.quand):'')+'</div>';
if(x.legs){x.legs.forEach(function(l){h+='<div class="note">'+esc(l.sel)+', '+esc(l.match)+' : '+fr(l.cote)+'</div>';});}
h+='</div><div class="prix"><div class="cote">'+(x.cote?fr(x.cote):'')+'</div>'+(x.cote?'':'<div class="mini">mini '+fr(x.mini)+'</div>')+'</div>'+
'<button class="retire" type="button" data-retire="'+esc(x.id)+'" aria-label="Retirer '+esc(x.sel)+'">×</button></div>';});
h+='</div>';
if(tot){h+='<div class="recap"><div class="note">Si tu les joues ensemble en un combiné</div><div class="t">'+fr(tot.cote)+'</div><div class="note">chance de passer estimée : '+pc(tot.p)+'</div>'+
(tot.double?'<div class="avert">Deux sélections portent sur le même match : Betclic peut refuser de les combiner.</div>':'')+'</div>';}
else if(t.length>1){h+='<div class="recap"><div class="note">Ce ticket mélange combinés et paris sans cote : joue-les en mises séparées.</div></div>';}
contenu.innerHTML=h;
contenu.querySelectorAll('[data-retire]').forEach(function(b){b.addEventListener('click',function(){
ecrire(lire().filter(function(x){return x.id!==b.getAttribute('data-retire');}));rafraichir();});});}
document.querySelectorAll('[data-item]').forEach(function(b){b.addEventListener('click',function(){
var it=JSON.parse(b.getAttribute('data-item')),t=lire(),i=t.findIndex(function(x){return x.id===it.id;});
if(i>=0){t.splice(i,1);}else{t.push(it);}ecrire(t);rafraichir();});});
function ouvrir(o){feuille.classList.toggle('ouvert',o);voile.classList.toggle('ouvert',o);feuille.setAttribute('aria-hidden',o?'false':'true');
if(o){feuille.focus();}}
document.getElementById('voir-ticket').addEventListener('click',function(){ouvrir(true);});
document.getElementById('fermer-ticket').addEventListener('click',function(){ouvrir(false);});
voile.addEventListener('click',function(){ouvrir(false);});
document.addEventListener('keydown',function(ev){if(ev.key==='Escape')ouvrir(false);});
document.getElementById('vider-ticket').addEventListener('click',function(){ecrire([]);rafraichir();message('Ticket vidé');});
document.getElementById('copier-ticket').addEventListener('click',function(){var t=lire(),tot=total(t);
var l=['Mes paris, ticket du '+document.body.getAttribute('data-jour')];
t.forEach(function(x){l.push('- '+x.sel+' ('+x.match+(x.quand?', '+x.quand:'')+') : '+(x.cote?fr(x.cote):'cote mini '+fr(x.mini)));
(x.legs||[]).forEach(function(g){l.push('    '+g.sel+' ('+g.match+') : '+fr(g.cote));});});
if(tot)l.push('Combiné de toutes les sélections : cote '+fr(tot.cote));var txt=l.join('\n');
function secours(){var a=document.createElement('textarea');a.value=txt;document.body.appendChild(a);a.select();
try{document.execCommand('copy');message('Liste copiée');}catch(e){message('Copie impossible');}a.remove();}
if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(txt).then(function(){message('Liste copiée');},secours);}else{secours();}});
rafraichir();
})();
"""

COCHE_SVG = ('<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M5 12.5l4.2 4.2L19 7" fill="none" '
             'stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"/></svg>')


def quand_court(dt) -> str:
    d = dt.astimezone(TZ)
    return f"{JOURS_COURTS[d.weekday()]} {d:%d/%m} à {d:%H:%M}"


def donut(p, taille=54, ep=7, texte=None, label=""):
    """Camembert en anneau : la part rouge = la probabilité."""
    r = (taille - ep) / 2
    circ = 2 * math.pi * r
    arc = max(0.0, min(1.0, p)) * circ
    c = taille / 2
    t = texte if texte is not None else pc(p).replace(" %", "%").replace("moins de 1%", "<1%")
    return (f'<svg class="donut" width="{taille}" height="{taille}" viewBox="0 0 {taille} {taille}" role="img" '
            f'aria-label="{e(label or pc(p))}"><circle cx="{c}" cy="{c}" r="{r:.2f}" fill="none" stroke="#E4E4E7" '
            f'stroke-width="{ep}"/><circle cx="{c}" cy="{c}" r="{r:.2f}" fill="none" stroke="#C1121F" '
            f'stroke-width="{ep}" stroke-dasharray="{arc:.2f} {circ:.2f}" transform="rotate(-90 {c} {c})"/>'
            f'<text x="{c}" y="{c + taille * 0.09:.1f}" text-anchor="middle" style="font-size:{taille * 0.24:.1f}px">{e(t)}</text></svg>')


def donut_parts(parts, taille=64, ep=9, label="", texte=""):
    """Camembert en anneau à plusieurs parts : [(valeur, couleur), ...], avec un texte au centre."""
    tot = sum(v for v, _ in parts) or 1
    r = (taille - ep) / 2
    circ = 2 * math.pi * r
    c, deb, arcs = taille / 2, 0.0, ""
    for v, coul in parts:
        lg = v / tot * circ
        if lg > 0:
            arcs += (f'<circle cx="{c}" cy="{c}" r="{r:.2f}" fill="none" stroke="{coul}" stroke-width="{ep}" '
                     f'stroke-dasharray="{lg:.2f} {circ:.2f}" stroke-dashoffset="{-deb:.2f}" transform="rotate(-90 {c} {c})"/>')
        deb += lg
    return (f'<svg class="donut" width="{taille}" height="{taille}" viewBox="0 0 {taille} {taille}" role="img" '
            f'aria-label="{e(label)}"><circle cx="{c}" cy="{c}" r="{r:.2f}" fill="none" stroke="#F7F7F8" '
            f'stroke-width="{ep}"/>{arcs}'
            + (f'<text x="{c}" y="{c + taille * 0.09:.1f}" text-anchor="middle" style="font-size:{taille * 0.24:.1f}px">'
               f'{e(texte)}</text>' if texte else "") + '</svg>')


def item_attr(item) -> str:
    return e(json.dumps(item, ensure_ascii=False, separators=(",", ":")))


def item_option(o) -> dict:
    return {"id": f'{o["match_id"]}|{o["libelle"]}', "sel": o["libelle"], "match": o["match"],
            "quand": quand_court(o["start"]), "cote": o["cote"], "p": round(o["p"], 4), "mid": str(o["match_id"])}


def bouton_pick(item) -> str:
    return (f'<button class="pick" type="button" aria-pressed="false" aria-label="Ajouter au ticket : {e(item["sel"])}" '
            f'data-item="{item_attr(item)}">{COCHE_SVG}</button>')


def ligne_pari(o, avec_donut=True) -> str:
    v, _, _ = verdict(o["p"])
    if o["statut"] == "VALUE":
        mise = f', mise {fr(o["mise"], 1)} % du capital' if o["mise"] > 0 else ""
        euros = f' ({fr(BANKROLL * o["mise"] / 100)} €)' if BANKROLL and mise else ""
        detail = f'<b>{pc(o["p"])}</b> de chance, <span class="r">+{round(100 * o["edge"])} % d\'avantage</span>{mise}{euros}'
    else:
        detail = f'<b>{pc(o["p"])}</b> de chance, {v.lower()}, cote un peu basse'
    al = f'<div class="alerte">{e(o["alerte"])}</div>' if o["alerte"] else ""
    return (f'<div class="carte"><div class="sel">{e(o["libelle"])}</div><div class="droite cote">{fr(o["cote"])}</div>'
            f'<div class="qui">{e(o["match"])}, {quand_court(o["start"])}</div>'
            f'<div class="droite mini">mini {fr(o["cote_min"])}</div>'
            f'<div class="bas">' + (donut(o["p"], taille=44, ep=6, label=f'Chance de gagner {pc(o["p"])}') if avec_donut else "")
            + f'<div class="txt">{detail}{al}</div>{bouton_pick(item_option(o))}</div></div>')


def ticket_combine(c, nom) -> str:
    item = {"id": "combi|" + "|".join(sorted(f'{o["match_id"]}:{o["libelle"]}' for o in c["legs"])),
            "sel": f"Combiné : {nom}", "match": f'{len(c["legs"])} matchs', "quand": "",
            "cote": round(c["cote"], 4), "p": round(c["p"], 5), "mids": sorted({str(o["match_id"]) for o in c["legs"]}),
            "legs": [{"sel": o["libelle"], "match": o["match"], "cote": o["cote"]} for o in c["legs"]]}
    jambes = "".join(f'<div class="jambe"><div><div class="sel" style="font-size:16px">{e(o["libelle"])}</div>'
                     f'<div class="qui">{e(o["match"])}, {quand_court(o["start"])}</div></div>'
                     f'<div class="c">{fr(o["cote"])}</div></div>' for o in c["legs"])
    renta = (f'<span class="renta ok">rentable, +{round(100 * c["ev"])} %</span>' if c["ev"] > 0
             else f'<span class="renta">pour le plaisir ({round(100 * c["ev"])} %)</span>')
    return (f'<div class="ticket"><div class="haut"><div class="nom">{e(nom)}</div>{bouton_pick(item)}</div>{jambes}'
            f'<div class="bas">{donut(c["p"], taille=50, ep=6, label=f"Chance de passer {pc(c["p"])}")}'
            f'<div class="quoi">chance de passer<br>{renta}</div>'
            f'<div style="text-align:right"><div class="total">{fr(c["cote"])}</div><div class="note">cote totale</div></div></div></div>')


def fiche_match(m) -> str:
    foot = m["cat"] == "FOOT"

    def equipe(nom, s):
        if not s:
            return f'<div class="equipe"><div class="n">{e(nom)}</div><div class="stat">Statistiques indisponibles</div></div>'
        niv = niveau_mot(s["badge"])
        if foot:
            v, n, d = (int(x) for x in s["VND"].split("-"))
            t = max(1, v + n + d)
            pv, pn, pd = round(100 * v / t), round(100 * n / t), round(100 * d / t)
            cam = donut_parts([(v, "#C1121F"), (n, "#A1A1AA"), (d, "#D4D4D8")], texte=f"{pv}%",
                              label=f"{pv} % de victoires, {pn} % de nuls, {pd} % de défaites")
            leg = (f'<div class="legende"><b style="color:#C1121F">{pv} % victoires</b><br>{pn} % nuls<br>'
                   f'{pd} % défaites<br>sur {s["MJ"]} matchs</div>')
            stats = (f'<div class="stat">Buts marqués <b>{fr(s["BM"], 1)}</b>, encaissés <b>{fr(s["BE"], 1)}</b> par match</div>'
                     f'<div class="stat">Plus de 2,5 buts <b>{pc(s["O25"])}</b>, les 2 marquent <b>{pc(s["BTTS"])}</b></div>'
                     f'<div class="stat">Victoires à domicile <b>{pc(s["pV_dom"])}</b>, à l\'extérieur <b>{pc(s["pV_ext"])}</b></div>')
        else:
            v, d = (int(x) for x in s["VD"].split("-"))
            t = max(1, v + d)
            pv, pd = round(100 * v / t), round(100 * d / t)
            cam = donut_parts([(v, "#C1121F"), (d, "#D4D4D8")], texte=f"{pv}%",
                              label=f"{pv} % de victoires, {pd} % de défaites")
            leg = (f'<div class="legende"><b style="color:#C1121F">{pv} % victoires</b><br>{pd} % défaites<br>'
                   f'{v}-{d} sur {s["MJ"]} matchs</div>')
            b2b = '<div class="alerte">2e match en 2 jours</div>' if s.get("repos") == 1 else ""
            stats = (f'<div class="stat">Points marqués <b>{fr(s["PM"], 1)}</b>, encaissés <b>{fr(s["PE"], 1)}</b></div>'
                     f'<div class="stat">Écart moyen <b>{fr(s["net"], 1)}</b></div>{b2b}')
        forme = "".join(f'<b class="{x}">{x}</b>' for x in s["forme"])
        return (f'<div class="equipe"><div class="n">{e(nom)}</div>'
                f'<div class="niveau{" fort" if niv == "FORT" else ""}">Niveau {niv.lower()}, {rang_txt(s["rang"])}</div>'
                f'<div class="camembert">{cam}{leg}</div><div class="forme" aria-label="5 derniers matchs">{forme}</div>{stats}</div>')
    opts = [o for o in m["options"] if o["groupe"] == "1N2"] + sorted(
        [o for o in m["options"] if o["groupe"] != "1N2"], key=lambda o: -o["edge"])[:2]
    puces = "".join(
        f'<button class="puce{" bon" if o["statut"] == "VALUE" else ""}" type="button" aria-pressed="false" '
        f'data-item="{item_attr(item_option(o))}">{e(o["libelle"].replace("Victoire ", ""))}<b>{fr(o["cote"])}</b></button>'
        for o in opts)
    notes = "".join(f'<div class="note">{e(n)}</div>' for n in m["notes"])
    if m.get("alerte"):
        notes += f'<div class="alerte">{e(m["alerte"])}</div>'
    attendus = f', buts attendus {fr(m["lam"])} à {fr(m["mu"])}' if m.get("lam") is not None else ""
    return (f'<article class="fiche"><div class="titre">{e(m["home"])} contre {e(m["away"])}</div>'
            f'<div class="qui">{e(m["comp"])}, {quand_court(m["start"])}{attendus}</div>'
            f'<div class="equipes">{equipe(m["home"], m.get("stats_h"))}{equipe(m["away"], m.get("stats_a"))}</div>'
            f'<div class="puces" aria-label="Cotes Betclic, à cocher">{puces}</div>{notes}</article>')


def initiales(nom) -> str:
    mots = [m for m in re.split(r"[\s\-]+", str(nom)) if m and m[0].isalpha()]
    return (mots[0][0] + (mots[-1][0] if len(mots) > 1 else "")).upper() if mots else "?"


def ligne_suggestion(item, texte, detail, p, mini) -> str:
    return (f'<div class="sugg">{donut(p, taille=40, ep=5, label=f"{pc(p)}")}<div class="corps"><div class="sel">{e(texte)}</div>'
            f'<div class="note">{detail}, joue si la cote est d\'au moins <b>{fr(mini)}</b></div></div>{bouton_pick(item)}</div>')


def carte_joueur(c, sport, pepite=False) -> str:
    m = c["match"]
    match_txt = f'{m["home"]} – {m["away"]}'
    base = {"match": match_txt, "quand": quand_court(m["start"]), "cote": None, "mid": str(m["id"])}
    if sport == "nba":
        r5, rs = c["r5"], c["rs"]

        def case(k, lib):
            haut = " haut" if r5[k] > rs[k] * 1.1 else ""
            return (f'<div><div class="v{haut}">{fr(r5[k], 1)}</div><div class="l">{lib}</div>'
                    f'<div class="avant">moy. {fr(rs[k], 1)}</div></div>')
        chiffres = case("pts", "points") + case("reb", "rebonds") + case("ast", "passes")
        sugg = ""
        for x in c["paris"]:
            mini = round(1.1 / x["taux"], 2)
            texte = f'Plus de {fr(x["ligne"], 1)} {x["stat"]}'
            item = {**base, "id": f'prop|{c["joueur"]}|{x["stat"]}|{x["ligne"]}', "sel": f'{c["joueur"]} : {texte.lower()}',
                    "mini": mini, "p": round(x["taux"], 3)}
            sugg += ligne_suggestion(item, texte, f'Passé {x["n"]} fois sur ses {x["sur"]} derniers matchs', x["taux"], mini)
        bio = phrase_nba(c, pepite)
    else:
        chiffres = (f'<div><div class="v">{c["buts"]}</div><div class="l">buts</div></div>'
                    f'<div><div class="v">{c["passes"]}</div><div class="l">passes déc.</div></div>'
                    f'<div><div class="v">{fr(c["g90"] + c["a90"], 2)}</div><div class="l">buts + passes / 90 min</div></div>')
        sugg = ""
        for cle, lib, p in (("but", "buteur", c["p_but"]), ("passe", "passeur décisif", c["p_passe"])):
            if p < 0.15:
                continue
            mini = round(1.1 / p, 2)
            item = {**base, "id": f'foot|{c["joueur"]}|{cle}', "sel": f'{c["joueur"]} {lib}', "mini": mini, "p": round(p, 3)}
            sugg += ligne_suggestion(item, f'{c["joueur"]} {lib}', f'{pc(p)} de chance s\'il joue', p, mini)
        bio = phrase_foot(c)
    etiquette = '<div class="etiquette">La pépite de la semaine</div>' if pepite else ""
    return (f'<article class="joueur{" pepite" if pepite else ""}"><div class="tete-j"><div class="avatar" aria-hidden="true">'
            f'{e(initiales(c["joueur"]))}</div><div class="corps">{etiquette}<div class="sel">{e(c["joueur"])}</div>'
            f'<div class="qui">{e(c["equipe"])}, contre {e(c["adversaire"])}, {quand_court(m["start"])}</div></div></div>'
            f'<div class="bio">{e(bio)}</div><div class="duo">{chiffres}</div>{sugg}</article>')


def onglet_joueurs(js) -> tuple[str, int]:
    if not js:
        return "", 0
    h, n = "", 0
    for sport, titre_s, aide in (
            ("nba", "Basket : en grande forme", "Points, rebonds et passes sur les 5 derniers matchs, comparés à leur moyenne. "
             "Les seuils sont ceux qu'ils ont dépassés au moins 7 fois sur 10 : compare-les aux lignes Betclic."),
            ("foot", "Foot : en grande forme", "Buts et passes décisives de la saison rapportés au temps de jeu.")):
        d = js.get(sport)
        if not d or not (d["forme"] or d["pepite"]):
            continue
        h += f"<h2>{titre_s}</h2><p class=\"aide\">{aide}</p>"
        if d["pepite"]:
            h += carte_joueur(d["pepite"], sport, pepite=True)
            n += 1
        for c in d["forme"]:
            h += carte_joueur(c, sport)
            n += 1
    return h, n


def page_onglets(v) -> str:
    """Page de l'icône « Mes paris » : onglets par type de pari, camemberts, ticket récapitulatif à cocher."""
    syn, now, fin = v["syn"], v["now"], v["fin"]
    matchs_f, matchs_b = v["matchs_f"], v["matchs_b"]
    a_jouer = syn["a_jouer"]

    def vide(t):
        return f'<p class="vide">{t}</p>'

    def titre(t, aide=""):
        return f"<h2>{t}</h2>" + (f'<p class="aide">{aide}</p>' if aide else "")

    # --- À jouer
    n_matchs = len(matchs_f) + len(matchs_b)
    if a_jouer:
        jouer = (f'<p class="intro">{len(a_jouer)} pari{"s" if len(a_jouer) > 1 else ""} sur {n_matchs} matchs ont une '
                 f'cote Betclic plus haute que leur vraie chance de passer. Coche ceux que tu veux jouer.</p>'
                 + '<div class="liste">' + "".join(ligne_pari(o) for o in a_jouer) + "</div>")
    else:
        jouer = vide(f"Aucune cote Betclic n'est assez haute cette semaine sur {n_matchs} matchs : le mieux est de ne rien jouer.")
    if syn["probables"]:
        jouer += (titre("Les plus sûrs", "Forte chance de passer, mais la cote est souvent trop basse pour être rentable.")
                  + '<div class="liste">' + "".join(ligne_pari(o, avec_donut=False) for o in syn["probables"]) + "</div>")
    jouer += ('<div class="liens">' + ('<a href="bilan.pdf">Ouvrir le PDF détaillé</a>' if v["avec_pdf"] else "")
              + '<a href="detail.html">Rapport complet</a></div>')

    # --- Buts
    lignes_buts = []
    for x in syn["buts"]:
        m, ch = x["match"], x["choix"]
        barres = "".join(
            f'<div class="barre{" choix" if l is ch else ""}"><span class="l">{l["libelle"].replace(" buts", "").replace("Plus de ", "+").replace("Moins de ", "−")}</span>'
            f'<span class="p"><i style="width:{round(100 * l["p"])}%"></i></span><span class="v">{pc(l["p"])}</span></div>'
            for l in x["lignes"] if l["sens"] == "Plus" or l is ch)
        item = (item_option(ch["opt"]) if ch["opt"] else
                {"id": f'{m["id"]}|{ch["libelle"]}', "sel": ch["libelle"], "match": f'{m["home"]} – {m["away"]}',
                 "quand": quand_court(m["start"]), "cote": None, "mini": round(ch["cote_min"] * 1.05, 2),
                 "p": round(ch["p"], 4), "mid": str(m["id"])})
        prix = (f'<div class="droite cote">{fr(ch["cote"])}</div><div class="droite mini">cote Betclic</div>' if ch["cote"]
                else f'<div class="droite cote" style="color:#A1A1AA">–</div><div class="droite mini">mini {fr(ch["cote_min"] * 1.05)}</div>')
        lignes_buts.append(
            f'<div class="carte"><div class="qui" style="margin:0;grid-column:1 / -1">{e(m["home"])} – {e(m["away"])}, '
            f'{quand_court(m["start"])}</div>'
            f'<div class="sel" style="margin-top:4px">{e(ch["libelle"])}</div>{prix.split("</div>", 1)[0]}</div>'
            f'<div class="note">{e(x["raison"].capitalize())}</div>{prix.split("</div>", 1)[1]}'
            f'<div class="bas"><div class="barres txt" style="margin:0">{barres}</div>{bouton_pick(item)}</div></div>')
    buts = (titre("Nombre de buts", "Notre conseil pour chaque match, et la chance de chaque ligne.")
            + '<div class="liste">' + "".join(lignes_buts) + "</div>") if lignes_buts else vide("Aucun match de foot retenu.")

    # --- Combinés
    groupes = groupes_combines(syn["comb"])
    std = [g for g in groupes if not g[0].startswith("Spécial")]
    ldc_g = [g for g in groupes if g[0].startswith("Spécial")]

    def bloc_combines(gs):
        h = ""
        for t, expl, combos in gs:
            if combos:
                h += titre(e(t), e(expl)) + "".join(ticket_combine(c, c.get("nom") or f"{t} n°{i}")
                                                     for i, c in enumerate(combos, 1))
        return h
    n_comb = sum(len(c) for _, _, c in std)
    combines = bloc_combines(std) if n_comb else vide("Aucune combinaison possible cette semaine.")

    # --- Buteurs
    buteurs = syn["buteurs"][:12]
    lignes_but = []
    for b in buteurs:
        mid = next((str(m["id"]) for m in matchs_f if f'{m["home"]} – {m["away"]}' == b["match"]), b["match"])
        item = {"id": f'{mid}|buteur|{b["joueur"]}', "sel": f'{b["joueur"]} buteur', "match": b["match"],
                "quand": quand_court(b["start"]), "cote": None, "mini": round(b["cote_min"] * 1.1, 2),
                "p": round(b["p"], 4), "mid": mid}
        inc = '<div class="alerte">Incertain pour ce match</div>' if b.get("douteux") else ""
        lignes_but.append(
            f'<div class="carte"><div class="sel">{e(b["joueur"])}</div><div class="droite cote">{fr(b["cote_min"] * 1.1)}</div>'
            f'<div class="qui">{e(b["equipe"])} contre {e(b["adv"])}, {quand_court(b["start"])}</div>'
            f'<div class="droite mini">cote mini</div>'
            f'<div class="bas">{donut(b["p"], taille=44, ep=6, label=f"Chance de marquer {pc(b["p"])}")}'
            f'<div class="txt"><b>{pc(b["p"])}</b> de chance de marquer, {b["buts"]} buts en {b["mj"]} matchs{inc}</div>'
            f'{bouton_pick(item)}</div></div>')
    but = (titre("Buteurs", "Chance de marquer s'il est titulaire. La cote buteur se vérifie sur Betclic.")
           + '<div class="liste">' + "".join(lignes_but) + "</div>") if lignes_but else vide("Pas de données buteurs cette semaine.")

    ldc_m = sorted([m for m in matchs_f if m["comp"] == "Ligue des Champions"], key=lambda m: m["start"])
    autres = sorted([m for m in matchs_f if m["comp"] != "Ligue des Champions"], key=lambda m: m["start"])
    onglets = [("jouer", "À jouer", len(a_jouer), jouer), ("buts", "Buts", len(lignes_buts), buts),
               ("combines", "Combinés", n_comb, combines)]
    if ldc_m:
        onglets.append(("ldc", "Ligue des Champions", len(ldc_m),
                        (bloc_combines(ldc_g) if ldc_g else "") + titre("Les matchs") + "".join(fiche_match(m) for m in ldc_m)))
    html_j, n_j = onglet_joueurs(syn.get("joueurs"))
    onglets += [("buteurs", "Buteurs", len(buteurs), but)]
    if n_j:
        onglets.append(("joueurs", "Joueurs", n_j, html_j + '<p class="aide" style="margin-top:16px">Les seuils et chances '
                        'viennent des matchs passés : ils ne garantissent rien. Vérifie que le joueur est bien titulaire.</p>'))
    onglets += [
                ("matchs", "Matchs", len(autres), (titre("Championnats", "Forme, bilan de la saison et cotes à cocher.")
                                                   + "".join(fiche_match(m) for m in autres)) if autres else vide("Aucun match."))]
    if matchs_b:
        bv = [o for o in a_jouer if o["cat"] == "BASKET"]
        onglets.append(("basket", "Basket", len(matchs_b),
                        ((titre("Paris basket à jouer") + '<div class="liste">' + "".join(ligne_pari(o) for o in bv) + "</div>")
                         if bv else "") + titre("Matchs NBA et EuroLeague")
                        + "".join(fiche_match(m) for m in sorted(matchs_b, key=lambda m: m["start"]))))

    rail = "".join(f'<button class="onglet" type="button" role="tab" id="t-{i}" aria-controls="p-{i}" aria-selected="false" '
                   f'data-onglet="{i}">{e(nom)}' + (f"<span>{n}</span>" if n else "") + "</button>"
                   for i, nom, n, _ in onglets)
    panneaux = "".join(f'<section role="tabpanel" id="p-{i}" aria-labelledby="t-{i}" data-panneau="{i}">{h}</section>'
                       for i, _, _, h in onglets)
    d0, d1 = now.astimezone(TZ), fin.astimezone(TZ)
    semaine = (f"Du {d0.day} au {d1.day} {MOIS_FR[d1.month - 1]}" if d0.month == d1.month
               else f"Du {d0.day} {MOIS_FR[d0.month - 1]} au {d1.day} {MOIS_FR[d1.month - 1]}")
    maj = datetime.now(TZ)
    ticket = (
        '<div class="barre-ticket" id="barre-ticket" aria-hidden="true"><div class="in">'
        '<div class="n"><span id="nb-ticket"></span><br><span style="opacity:.85;font-size:13px">ton ticket</span></div>'
        '<div class="t" id="cote-ticket"></div><button type="button" id="voir-ticket">Voir le ticket</button></div></div>'
        '<div class="voile" id="voile"></div>'
        '<div class="feuille" id="feuille" role="dialog" aria-modal="true" aria-labelledby="titre-ticket" aria-hidden="true" tabindex="-1">'
        '<div class="in"><div class="poignee"></div><div style="display:flex;justify-content:space-between;align-items:center">'
        '<h2 id="titre-ticket">Ton ticket</h2><button type="button" class="btn texte" id="fermer-ticket">Fermer</button></div>'
        '<p class="aide">Retrouve ces sélections sur Betclic. Les cotes ont pu bouger depuis le bilan.</p>'
        '<div id="contenu-ticket"></div><div class="actions">'
        '<button type="button" class="btn plein" id="copier-ticket">Copier la liste</button>'
        '<a class="btn creux" href="https://www.betclic.fr/" target="_blank" rel="noopener">Ouvrir Betclic</a>'
        '<button type="button" class="btn texte" id="vider-ticket">Vider le ticket</button></div></div></div>'
        '<div class="info" id="info" role="status" aria-live="polite"></div>')
    return (
        '<!doctype html><html lang="fr"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><title>Mes paris</title>'
        '<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes">'
        '<meta name="apple-mobile-web-app-title" content="Mes paris"><meta name="theme-color" content="#FFFFFF">'
        '<link rel="apple-touch-icon" href="apple-touch-icon.png"><link rel="icon" href="icon.png">'
        '<link rel="manifest" href="manifest.json">'
        '<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>'
        '<link href="https://fonts.googleapis.com/css2?family=Barlow:wght@400;500;600&family=Barlow+Semi+Condensed:wght@500;600;700&display=swap" rel="stylesheet">'
        f'<style>{APPLI_CSS}</style></head>'
        f'<body data-semaine="{now.astimezone(TZ):%Y%m%d%H%M}" data-jour="{d0:%d/%m}">'
        f'<header class="page tete"><div class="marque"><i aria-hidden="true"></i><h1>Mes paris</h1></div>'
        f'<div class="semaine">Matchs {semaine[0].lower()}{semaine[1:]}</div>'
        f'<div class="maj">Mis à jour le {maj.day} {MOIS_FR[maj.month - 1]} à {maj:%H:%M}</div></header>'
        f'<div class="page"><!--COMPOS--></div>'
        f'<nav class="onglets" aria-label="Types de paris"><div class="rail" role="tablist">{rail}</div></nav>'
        f'<main class="page">{panneaux}<p class="pied">Ces chiffres sont des estimations : même un bon pari perd souvent. '
        f"Ne mise que ce que tu peux perdre. Besoin d'aide : Joueurs Info Service, 09 74 75 13 13.</p></main>"
        f'{ticket}<script>{APPLI_JS}</script></body></html>')


# =============================================================================
# PDF : rapport détaillé (reportlab, pur Python)
# =============================================================================
def pdf_txt(s) -> str:
    """Texte sûr pour les polices PDF standard (accents français OK, autres caractères translittérés)."""
    out = []
    for ch in str(s):
        try:
            ch.encode("cp1252")
            out.append(ch)
        except UnicodeEncodeError:
            out.append(unicodedata.normalize("NFKD", ch).encode("ascii", "ignore").decode() or "?")
    return html.escape("".join(out), quote=False)


def generer_pdf(chemin, matchs_f, matchs_b, syn, src, now, fin) -> bool:
    try:
        from reportlab.lib import colors
        from reportlab.lib.enums import TA_CENTER
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.styles import ParagraphStyle
        from reportlab.lib.units import mm
        from reportlab.platypus import (KeepTogether, PageBreak, Paragraph, SimpleDocTemplate, Spacer, Table,
                                        TableStyle)
    except Exception as ex:
        log(f"   PDF non généré : reportlab manquant ({ex}). Lance : python -m pip install reportlab")
        src.echecs.append("PDF (reportlab non installé)")
        return False

    VERT, ROUGE, AMBRE, BLEU = colors.HexColor("#0f7b3f"), colors.HexColor("#b42318"), colors.HexColor("#9a5b00"), colors.HexColor("#1a56db")
    GRIS, BORD, FOND = colors.HexColor("#5f6b7a"), colors.HexColor("#d9dee5"), colors.HexColor("#f2f4f7")
    FOOT, BASKET = colors.HexColor("#14532d"), colors.HexColor("#9a3412")
    st = {
        "h1": ParagraphStyle("h1", fontName="Helvetica-Bold", fontSize=22, leading=27, spaceAfter=2),
        "sous": ParagraphStyle("sous", fontName="Helvetica", fontSize=10.5, leading=14, textColor=GRIS),
        "h2": ParagraphStyle("h2", fontName="Helvetica-Bold", fontSize=15, leading=19, spaceBefore=14, spaceAfter=3,
                             keepWithNext=1),
        "intro": ParagraphStyle("intro", fontName="Helvetica", fontSize=10, leading=13.5, textColor=GRIS, spaceAfter=6,
                                keepWithNext=1),
        "p": ParagraphStyle("p", fontName="Helvetica", fontSize=10.5, leading=14.5),
        "cell": ParagraphStyle("cell", fontName="Helvetica", fontSize=9.5, leading=12.5),
        "cellb": ParagraphStyle("cellb", fontName="Helvetica-Bold", fontSize=10, leading=13),
        "petit": ParagraphStyle("petit", fontName="Helvetica", fontSize=8.5, leading=11, textColor=GRIS),
        "th": ParagraphStyle("th", fontName="Helvetica-Bold", fontSize=8.5, leading=11, textColor=GRIS),
        "gros": ParagraphStyle("gros", fontName="Helvetica-Bold", fontSize=18, leading=22, alignment=TA_CENTER),
        "leg": ParagraphStyle("leg", fontName="Helvetica", fontSize=8.5, leading=11, textColor=GRIS, alignment=TA_CENTER),
        "bandeau": ParagraphStyle("bandeau", fontName="Helvetica-Bold", fontSize=14, leading=18, textColor=colors.white),
    }
    LARG = A4[0] - 30 * mm
    P = lambda t, s="cell": Paragraph(t, st[s])

    def coul(c):
        return c.hexval().replace("0x", "#")

    def verdict_p(p):
        v, fg, _ = verdict(p)
        return f'<font color="{fg}"><b>{pdf_txt(v)}</b></font>'

    def tableau(entetes, lignes, largeurs, vide):
        if not lignes:
            return [P(pdf_txt(vide), "intro")]
        data = [[P(pdf_txt(h), "th") for h in entetes]] + lignes
        t = Table(data, colWidths=[w * LARG for w in largeurs], repeatRows=1)
        t.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, 0), FOND), ("LINEBELOW", (0, 0), (-1, -1), 0.5, BORD),
            ("BOX", (0, 0), (-1, -1), 0.5, BORD), ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("TOPPADDING", (0, 0), (-1, -1), 5), ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
            ("LEFTPADDING", (0, 0), (-1, -1), 6), ("RIGHTPADDING", (0, 0), (-1, -1), 6)]))
        return [t]

    def pari_cell(o):
        al = f'<br/><font color="{coul(ROUGE)}">Attention : {pdf_txt(o["alerte"])}</font>' if o["alerte"] else ""
        return P(f'<b>{pdf_txt(o["libelle"])}</b><br/><font size="8.5" color="{coul(GRIS)}">'
                 f'{pdf_txt(o["match"])} · {pdf_txt(o["comp"])} · {pdf_txt(heure(o["start"]))}</font>{al}')

    def forme_pdf(s):
        c = {"V": coul(VERT), "N": "#8a94a3", "D": coul(ROUGE)}
        return " ".join(f'<font color="{c.get(x, "#999999")}"><b>{x}</b></font>' for x in s) or "–"

    def bandeau(texte, couleur):
        t = Table([[P(pdf_txt(texte), "bandeau")]], colWidths=[LARG])
        t.setStyle(TableStyle([("BACKGROUND", (0, 0), (-1, -1), couleur), ("TOPPADDING", (0, 0), (-1, -1), 7),
                               ("BOTTOMPADDING", (0, 0), (-1, -1), 7), ("LEFTPADDING", (0, 0), (-1, -1), 10)]))
        return [Spacer(1, 6), t, Spacer(1, 4)]

    el = []
    # ---------------- page 1 : résumé ----------------
    el += [P("Bilan Betclic de la semaine", "h1"),
           P(pdf_txt(f"Matchs du {now.astimezone(TZ):%d/%m/%Y} au {fin.astimezone(TZ):%d/%m/%Y} · "
                     f"rapport créé le {datetime.now(TZ):%d/%m/%Y à %H:%M}"), "sous"), Spacer(1, 10)]
    chiffres = [(str(len(matchs_f)), "matchs de foot"), (str(len(matchs_b)), "matchs de basket"),
                (str(len(syn["a_jouer"])), "paris à jouer"), (pdf_txt(src.quota), "crédits API restants")]
    t = Table([[P(v, "gros") for v, _ in chiffres], [P(pdf_txt(l), "leg") for _, l in chiffres]],
              colWidths=[LARG / 4] * 4)
    t.setStyle(TableStyle([("BOX", (0, 0), (-1, -1), 0.5, BORD), ("INNERGRID", (0, 0), (-1, -1), 0.5, BORD),
                           ("LINEBELOW", (0, 0), (-1, 0), 0, colors.white), ("BACKGROUND", (0, 0), (-1, -1), colors.white),
                           ("TOPPADDING", (0, 0), (-1, -1), 6), ("BOTTOMPADDING", (0, 0), (-1, -1), 6)]))
    el += [t, Spacer(1, 10)]
    lex = [
        ("Chance de gagner", "probabilité estimée par le modèle statistique et le marché Pinnacle (le bookmaker le plus fiable)."),
        ("Cote mini rentable", "la cote à partir de laquelle le pari gagne de l'argent à long terme (1 / chance de gagner)."),
        ("Avantage", "de combien la cote Betclic dépasse la cote mini rentable. On ne retient un pari qu'à partir de "
                     f"+{round(100 * EDGE_MIN)} %."),
        ("Mise conseillée", f"en % de ton capital, plafonnée à {fr(MISE_MAX_PCT, 1)} %."),
        ("Niveau d'équipe", "FORT / MOYEN / FAIBLE = tiers du classement de force calculé par le modèle."),
    ]
    t = Table([[P(f"<b>{pdf_txt(a)}</b>"), P(pdf_txt(b))] for a, b in lex], colWidths=[0.24 * LARG, 0.76 * LARG])
    t.setStyle(TableStyle([("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#eef3fd")), ("VALIGN", (0, 0), (-1, -1), "TOP"),
                           ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]))
    el += [P("Comment lire ce rapport", "h2"), t]
    if getattr(src, "perimetre", None):
        t = Table([[P(f"<b>{pdf_txt(n)}</b>"), P(pdf_txt(txt))] for n, txt in src.perimetre],
                  colWidths=[0.24 * LARG, 0.76 * LARG])
        t.setStyle(TableStyle([("LINEBELOW", (0, 0), (-1, -1), 0.3, BORD), ("VALIGN", (0, 0), (-1, -1), "TOP"),
                               ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]))
        el += [P("Matchs analysés cette semaine", "h2"),
               P("Seuls les matchs impliquant ces clubs sont retenus. Aucun championnat italien.", "intro"), t]

    # ---------------- 1. paris à jouer ----------------
    el += [P("1. Les paris à jouer", "h2"),
           P("La cote Betclic est plus haute que la vraie chance de gagner. Classés du plus sûr au plus risqué.", "intro")]
    lignes = [[pari_cell(o), P(f'<b><font size="12">{fr(o["cote"])}</font></b>'),
               P(f'<b>{pc(o["p"])}</b><br/>{verdict_p(o["p"])}'), P(fr(o["cote_min"])),
               P(f'<font color="{coul(VERT)}"><b>+{round(100 * o["edge"])} %</b></font>'),
               P(f'{fr(o["mise"], 1)} %' + (f'<br/>{fr(BANKROLL * o["mise"] / 100)} €' if BANKROLL else ""))]
              for o in syn["a_jouer"][:15]]
    el += tableau(["Pari", "Cote", "Chance de gagner", "Cote mini rentable", "Avantage", "Mise"], lignes,
                  [0.40, 0.09, 0.15, 0.13, 0.11, 0.12],
                  "Aucune cote Betclic n'est assez haute cette semaine. Le plus sage est de ne rien jouer.")
    douteux = [o for o in syn["value"] if o["alerte"]] + syn["suspects"]
    if douteux:
        el += [Spacer(1, 4), P(pdf_txt("Écartés malgré une bonne cote (blessure signalée ou écart trop grand pour être fiable) : "
                         + " ; ".join(f'{o["libelle"]} ({o["match"]})' for o in douteux[:6])), "petit")]

    # ---------------- 1 bis. nombre de buts ----------------
    el += [P("Nombre de buts : match par match", "h2"),
           P("Chance de chaque ligne d'après le modèle et le marché. Entre parenthèses : la cote Betclic quand elle est "
             "proposée ; sinon, joue seulement si la cote affichée sur Betclic dépasse la cote mini.", "intro")]
    lignes = []
    for x in syn["buts"]:
        m, ch = x["match"], x["choix"]
        def case(l, sens):
            l2 = next((y for y in x["lignes"] if y["ligne"] == l and y["sens"] == sens), None)
            if not l2:
                return P("–")
            c = f'{fr(l2["cote"])}' if l2["cote"] else f'mini {fr(l2["cote_min"])}'
            gras = l2 is ch
            return P((f'<font color="{coul(VERT)}"><b>' if gras else "") + f'{pc(l2["p"])}<br/>'
                     f'<font size="8">{c}</font>' + ("</b></font>" if gras else ""))
        cote_ch = fr(ch["cote"]) if ch["cote"] else f'mini {fr(ch["cote_min"])}'
        lignes.append([P(f'<b>{pdf_txt(m["home"])} - {pdf_txt(m["away"])}</b><br/><font size="8.5" color="{coul(GRIS)}">'
                         f'{pdf_txt(m["comp"])} · {pdf_txt(heure(m["start"]))}</font>'),
                       case(1.5, "Plus"), case(2.5, "Plus"), case(3.5, "Plus"), case(3.5, "Moins"),
                       P(f'<b>{pdf_txt(ch["libelle"])}</b><br/>{cote_ch} · {pc(ch["p"])}<br/>'
                         f'<font size="8" color="{coul(GRIS)}">{pdf_txt(x["raison"])}</font>')])
    el += tableau(["Match", "+1,5 buts", "+2,5 buts", "+3,5 buts", "-3,5 buts", "Conseil"], lignes,
                  [0.30, 0.11, 0.11, 0.11, 0.11, 0.26], "Aucun match de foot retenu cette semaine.")

    # ---------------- 2. combinés ----------------
    el += [P("2. Les combinés", "h2"),
           P("Plusieurs paris sur le même ticket : tous doivent passer. Une seule sélection par match. "
             "Rentabilité négative = la marge de Betclic pèse plus que l'avantage : pari plaisir.", "intro")]
    for titre_g, expl, combos in groupes_combines(syn["comb"]):
        tete = [Spacer(1, 4), P(f"<b>{pdf_txt(titre_g)}</b>", "p"), P(pdf_txt(expl), "petit")]
        if not combos:
            el += tete + [P("Aucune combinaison possible cette semaine.", "intro")]
        for i_c, c in enumerate(combos):
            rows = [[P(f'<b>{pdf_txt(o["libelle"])}</b> <font size="8.5" color="{coul(GRIS)}">· {pdf_txt(o["match"])} · '
                       f'{pdf_txt(heure(o["start"]))}</font>'), P(f'<b>{fr(o["cote"])}</b>'), P(pc(o["p"]))]
                    for o in c["legs"]]
            ev_c = coul(VERT) if c["ev"] > 0 else coul(ROUGE)
            entete = [[P(f'<b>{pdf_txt(c["nom"])}</b>'), "", ""]] if c.get("nom") and c["nom"] != titre_g else []
            rows = entete + rows + [[P(f'<b>Cote totale {fr(c["cote"])}</b> · chance de passer <b>{pc(c["p"])}</b> · '
                                       f'rentabilité <font color="{ev_c}"><b>{round(100 * c["ev"]):+d} %</b></font>'), "", ""]]
            t = Table(rows, colWidths=[0.72 * LARG, 0.13 * LARG, 0.15 * LARG])
            stl = [("BOX", (0, 0), (-1, -1), 0.5, BORD), ("LINEBELOW", (0, 0), (-1, -2), 0.3, BORD),
                   ("SPAN", (0, -1), (-1, -1)), ("BACKGROUND", (0, -1), (-1, -1), FOND),
                   ("TOPPADDING", (0, 0), (-1, -1), 4), ("BOTTOMPADDING", (0, 0), (-1, -1), 4)]
            if entete:
                stl += [("SPAN", (0, 0), (-1, 0)), ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#eef3fd"))]
            t.setStyle(TableStyle(stl))
            el += [KeepTogether((tete if i_c == 0 else []) + [Spacer(1, 4), t]), Spacer(1, 4)]

    # ---------------- 3. les plus sûrs ----------------
    el += [P("3. Les plus sûrs (même sans avantage)", "h2"),
           P("Les sélections avec la plus forte chance de passer. Si l'avantage est négatif, la cote est trop basse "
             "pour être rentable à long terme.", "intro")]
    lignes = [[pari_cell(o), P(fr(o["cote"])), P(f'<b>{pc(o["p"])}</b><br/>{verdict_p(o["p"])}'),
               P(f'<font color="{coul(VERT) if o["edge"] > 0 else coul(GRIS)}">{round(100 * o["edge"]):+d} %</font>')]
              for o in syn["probables"]]
    el += tableau(["Pari", "Cote", "Chance de gagner", "Avantage"], lignes, [0.55, 0.12, 0.19, 0.14],
                  "Rien au-dessus de 60 % de chance cette semaine.")

    # ---------------- 4. buteurs ----------------
    el += [P("4. Buteurs", "h2"),
           P("Chance de marquer s'il est titulaire, d'après ses tirs (xG) et la défense adverse. Les cotes buteurs "
             "Betclic ne sont pas dans l'API : joue seulement si la cote affichée dépasse la cote minimale.", "intro")]
    lignes = [[P(f'<b>{pdf_txt(b["joueur"])}</b><br/><font size="8.5" color="{coul(GRIS)}">{pdf_txt(b["equipe"])} contre '
                 f'{pdf_txt(b["adv"])} · {pdf_txt(heure(b["start"]))}</font>'),
               P(f'<b>{pc(b["p"])}</b>'), P(f'<b>{fr(b["cote_min"] * 1.1)}</b>'),
               P(pdf_txt(f'{b["buts"]} buts en {b["mj"]} matchs · {round(b["min"])} min par match'))]
              for b in syn["buteurs"][:12]]
    el += tableau(["Joueur", "Chance de marquer", "Joue si cote au moins", "Sa saison"], lignes,
                  [0.40, 0.16, 0.18, 0.26], "Pas de données buteurs pour les matchs de la semaine.")

    # ---------------- 5. outsiders ----------------
    def outsiders_pdf(outs, titre_o):
        lignes = []
        for x in outs:
            s, o, adv = x["st"], x["opt"], x["adv"]
            detail = (f'{pc(s["pV"])} de victoires · +2,5 buts : {pc(s["O25"])}' if "O25" in s
                      else f'{pc(s["pV"])} de victoires · écart moyen {fr(s["net"], 1)} pts')
            lignes.append([P(f'<b>{pdf_txt(x["equipe"])}</b><br/><font size="8.5" color="{coul(GRIS)}">{pdf_txt(x["match"])}</font>'),
                           P(f'{forme_pdf(s["forme"])}<br/><font size="8.5">{pdf_txt(detail)}</font>'),
                           P(pdf_txt(f'{niveau_mot(adv.get("badge"))} ({rang_txt(adv.get("rang"))})') if adv else "–"),
                           P((f'{fr(o["cote"])} · {pc(o["p"])}' if o else "–"))])
        return [P(f"<b>{pdf_txt(titre_o)}</b>", "p")] + tableau(
            ["Équipe", "5 derniers matchs", "Adversaire", "Sa victoire"], lignes, [0.30, 0.32, 0.18, 0.20],
            "Aucune équipe moins en vue n'est en grande forme cette semaine.")
    el += [P("5. Équipes moins en vue en forme", "h2"),
           P("Hors du premier tiers du classement de force, mais en série positive.", "intro")]
    el += outsiders_pdf(syn["out_f"], "Football") + outsiders_pdf(syn["out_b"], "Basket")

    # ---------------- 6-7. tous les matchs ----------------
    def bloc_match(m):
        foot = m["cat"] == "FOOT"
        sh, sa = m.get("stats_h") or {}, m.get("stats_a") or {}

        def val(s, k, f=pc):
            return f(s[k]) if s and k in s else "–"
        if foot:
            rows = [("Niveau", lambda s: f'{niveau_mot(s["badge"])} ({rang_txt(s["rang"])})'),
                    ("5 derniers matchs", lambda s: forme_pdf(s["forme"])),
                    ("Bilan saison (V-N-D)", lambda s: f'{s["VND"]} en {s["MJ"]} matchs'),
                    ("Victoires à domicile / à l'extérieur", lambda s: f'{pc(s["pV_dom"])} / {pc(s["pV_ext"])}'),
                    ("Buts marqués / encaissés par match", lambda s: f'{fr(s["BM"], 1)} / {fr(s["BE"], 1)}'),
                    ("Buts marqués contre le top 6", lambda s: f'{fr(s["BM_top6"], 1)} par match'),
                    ("Matchs à plus de 2,5 buts", lambda s: pc(s["O25"])),
                    ("Les 2 équipes marquent", lambda s: pc(s["BTTS"])),
                    ("Matchs sans encaisser", lambda s: pc(s["CS"]))]
        else:
            rows = [("Niveau", lambda s: f'{niveau_mot(s["badge"])} ({rang_txt(s["rang"])})'),
                    ("5 derniers matchs", lambda s: forme_pdf(s["forme"])),
                    ("Bilan saison (V-D)", lambda s: f'{s["VD"]} en {s["MJ"]} matchs'),
                    ("Victoires à domicile / à l'extérieur", lambda s: f'{pc(s["pV_dom"])} / {pc(s["pV_ext"])}'),
                    ("Points marqués / encaissés", lambda s: f'{fr(s["PM"], 1)} / {fr(s["PE"], 1)}'),
                    ("Écart moyen", lambda s: f'{s["net"]:+.1f}'.replace(".", ",")),
                    ("Repos avant le match", lambda s: ("2e match en 2 jours" if s.get("repos") == 1
                                                         else f'{s.get("repos", "–")} jours'))]

        def cel(s, f):
            try:
                return P(f(s) if s else "–")
            except Exception:
                return P("–")
        entete = (f'<b><font size="12">{pdf_txt(m["home"])} - {pdf_txt(m["away"])}</font></b><br/>'
                  f'<font size="8.5" color="{coul(GRIS)}">{pdf_txt(m["comp"])} · {pdf_txt(heure(m["start"]))}'
                  + (f' · buts attendus {fr(m["lam"])} - {fr(m["mu"])}' if m.get("lam") is not None else "") + "</font>")
        data = [[P(entete), "", ""], [P(""), P(f'<b>{pdf_txt(m["home"])}</b>'), P(f'<b>{pdf_txt(m["away"])}</b>')]]
        data += [[P(pdf_txt(lbl), "petit"), cel(sh, f), cel(sa, f)] for lbl, f in rows]
        opts = [o for o in m["options"] if o["groupe"] == "1N2"] + sorted(
            [o for o in m["options"] if o["groupe"] != "1N2"], key=lambda o: -o["edge"])[:2]
        cotes = "&nbsp;&nbsp;<font color=\"#b8c0cc\">|</font>&nbsp;&nbsp;".join(
            (f'<font color="{coul(VERT)}">' if o["statut"] == "VALUE" else "<font>")
            + f'{pdf_txt(o["libelle"])} <b>{fr(o["cote"])}</b> ({pc(o["p"])})'
            + (" <b>[à jouer]</b>" if o["statut"] == "VALUE" else "") + "</font>" for o in opts)
        data.append([P(f"<b>Cotes Betclic</b> (chance) : {cotes}"), "", ""])
        notes = list(m["notes"]) + ([f'Attention : {m["alerte"]}'] if m.get("alerte") else [])
        if not m.get("alerte") and m.get("blesses"):
            notes.append("Incertains : " + ", ".join(m["blesses"]))
        if notes:
            data.append([P(f'<font color="{coul(AMBRE)}">{pdf_txt(" · ".join(notes))}</font>', "petit"), "", ""])
        t = Table(data, colWidths=[0.32 * LARG, 0.34 * LARG, 0.34 * LARG])
        stl = [("SPAN", (0, 0), (-1, 0)), ("BACKGROUND", (0, 0), (-1, 0), FOND),
               ("SPAN", (0, len(rows) + 2), (-1, len(rows) + 2)), ("BOX", (0, 0), (-1, -1), 0.6, BORD),
               ("LINEBELOW", (0, 1), (-1, -1), 0.3, BORD), ("VALIGN", (0, 0), (-1, -1), "TOP"),
               ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]
        if notes:
            stl.append(("SPAN", (0, -1), (-1, -1)))
        t.setStyle(TableStyle(stl))
        return [KeepTogether([t]), Spacer(1, 8)]

    for titre_s, couleur, ms in (("Football européen : tous les matchs", FOOT, matchs_f),
                                 ("Basket (NBA et EuroLeague) : tous les matchs", BASKET, matchs_b)):
        el += [PageBreak()] + bandeau(titre_s, couleur)
        if not ms:
            el.append(P("Aucun match dans la période.", "intro"))
        for m in sorted(ms, key=lambda x: x["start"]):
            el += bloc_match(m)

    erreurs = list(dict.fromkeys(src.echecs))
    if erreurs:
        el += [P("Données manquantes", "h2"), P(pdf_txt(" · ".join(erreurs)), "petit")]
    el += [Spacer(1, 10), P(pdf_txt("Ces chiffres sont des estimations : même un bon pari perd souvent, et les séries "
                                   "perdantes sont normales. Ne mise que ce que tu peux perdre. "
                                   "Joueurs Info Service : 09 74 75 13 13."), "petit")]

    def pied(canvas, doc):
        canvas.saveState()
        canvas.setFont("Helvetica", 8)
        canvas.setFillColor(GRIS)
        canvas.drawString(15 * mm, 10 * mm, pdf_txt(f"Bilan Betclic · {now.astimezone(TZ):%d/%m/%Y}"))
        canvas.drawRightString(A4[0] - 15 * mm, 10 * mm, f"page {doc.page}")
        canvas.restoreState()

    doc = SimpleDocTemplate(str(chemin), pagesize=A4, leftMargin=15 * mm, rightMargin=15 * mm,
                            topMargin=14 * mm, bottomMargin=16 * mm, title="Bilan Betclic", author="agent_betclic")
    doc.build(el, onFirstPage=pied, onLaterPages=pied)
    return True


def rang_txt(r) -> str:
    return "–" if r is None else ("1er" if r == 1 else f"{r}e")


def niveau_mot(b) -> str:
    return {"SOLIDE": "FORT", "MOYEN": "MOYEN", "FAIBLE": "FAIBLE"}.get(b, "–")


def ecrire_icone(dossier: Path) -> None:
    """Icône de l'« appli » (écran d'accueil iPhone / Android) + manifeste."""
    try:
        from PIL import Image, ImageDraw
    except Exception:
        return
    n = 512
    img = Image.new("RGB", (n, n), "#14532d")
    dr = ImageDraw.Draw(img)
    for i in range(n):                                   # léger dégradé vertical
        dr.line([(0, i), (n, i)], fill=(20, 83 + int(30 * i / n), 45 + int(15 * i / n)))
    dr.ellipse([96, 96, 416, 416], outline="white", width=26)            # le ballon / la cible
    dr.line([(178, 262), (238, 322), (346, 196)], fill="white", width=40, joint="curve")  # la coche
    for x, y in ((178, 262), (238, 322), (346, 196)):
        dr.ellipse([x - 20, y - 20, x + 20, y + 20], fill="white")
    img.save(dossier / "icon.png")
    img.resize((180, 180), Image.LANCZOS).save(dossier / "apple-touch-icon.png")
    (dossier / "manifest.json").write_text(json.dumps({
        "name": "Mes paris", "short_name": "Mes paris", "start_url": "./", "display": "standalone",
        "background_color": "#f5f7fa", "theme_color": "#14532d",
        "icons": [{"src": "icon.png", "sizes": "512x512", "type": "image/png"}]}, ensure_ascii=False), encoding="utf-8")


# =============================================================================
# ENVOI DE L'E-MAIL (avec le PDF en pièce jointe)
# =============================================================================
def envoyer_email(contenu_html: str, sujet: str, pdf: Path | None) -> None:
    msg = EmailMessage()
    msg["Subject"] = sujet
    msg["From"] = GMAIL_USER
    msg["To"] = GMAIL_USER
    msg.set_content("Ouvre le PDF joint pour voir le bilan de la semaine.")
    msg.add_alternative(contenu_html, subtype="html")
    if pdf is not None and pdf.exists():
        msg.add_attachment(pdf.read_bytes(), maintype="application", subtype="pdf", filename=pdf.name)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)
        smtp.send_message(msg)


# =============================================================================
# MODE AVANT-MATCH : contrôle léger les jours de match (compos officielles, blessures du jour)
# =============================================================================
F_CONSEILS = "conseils.json"          # écrit par le bilan, lu par le contrôle avant-match
F_STATUTS = "statuts_matchs.json"     # ce que les contrôles ont déjà vu
F_ALERTES = "alertes_envoyees.json"   # pour ne jamais envoyer deux fois la même alerte
FENETRE_COMPO_MIN = 75                # on cherche la compo dans les 75 minutes avant le coup d'envoi
FENETRE_BLESSURES_H = 48              # blessures vérifiées une fois par jour pour les matchs des 48 h à venir


def _lire_json(nom, defaut):
    try:
        return json.loads((CACHE_DIR / nom).read_text(encoding="utf-8"))
    except Exception:
        return defaut


def _ecrire_json(nom, data):
    CACHE_DIR.mkdir(exist_ok=True)
    (CACHE_DIR / nom).write_text(json.dumps(data, ensure_ascii=False, indent=1, default=str), encoding="utf-8")


def sauver_conseils(matchs_f, syn, now):
    """Mémorise ce que le bilan a conseillé, pour que le contrôle avant-match sache quoi surveiller."""
    comp_id = {c["nom"]: c["id"] for c in COMPETITIONS}
    matchs = {}
    for m in matchs_f:
        matchs[str(m["id"])] = {"home": m["home"], "away": m["away"], "start": m["start"].isoformat(),
                                "comp": m["comp"], "comp_id": comp_id.get(m["comp"]),
                                "fixture_id": m.get("fixture_id"), "cles": m.get("cles", {"home": [], "away": []}),
                                "absents_connus": [x["nom"] for x in m.get("absents", [])]}
    conseils = []

    def ajoute(o, type_, groupe):
        if str(o["match_id"]) in matchs:
            conseils.append({"match_id": str(o["match_id"]), "libelle": o["libelle"], "cote": o["cote"],
                             "type": type_, "groupe": groupe})
    for o in syn["a_jouer"]:
        ajoute(o, "simple", "Paris à jouer")
    for x in syn["buts"]:
        if x["choix"]["opt"]:
            ajoute(x["choix"]["opt"], "buts", "Nombre de buts")
    for titre, _, combos in groupes_combines(syn["comb"]):
        for i, c in enumerate(combos, 1):
            if titre.startswith("Spécial"):
                nom = f"LDC : {c.get('nom') or titre}"
            elif titre.startswith("Combiné global"):
                nom = "Combiné global"
            else:
                nom = f"{titre} n°{i}"
            for o in c["legs"]:
                ajoute(o, "combine", nom)
    for b in syn["buteurs"][:12]:
        mid = next((k for k, v in matchs.items() if f'{v["home"]} – {v["away"]}' == b["match"]), None)
        if mid:
            conseils.append({"match_id": mid, "libelle": f'{b["joueur"]} buteur', "cote": None, "type": "buteur",
                             "groupe": "Buteurs", "joueur": b["joueur"], "equipe": b["equipe"]})
    _ecrire_json(F_CONSEILS, {"cree": now.isoformat(), "matchs": matchs, "conseils": conseils})
    _ecrire_json(F_STATUTS, {})                 # nouvelle semaine : on repart de zéro
    _ecrire_json(F_ALERTES, [])


def conseils_touches(conseils, mid, joueur, cote_eq, info):
    """Les conseils d'un match qu'une absence fragilise : sa victoire, les « plus de » buts, le joueur buteur."""
    equipe = info[cote_eq]
    out = []
    for c in conseils:
        if c["match_id"] != mid:
            continue
        if c["type"] == "buteur":
            if meme_joueur(c["joueur"], joueur):
                out.append(c)
        elif c["libelle"].startswith("Victoire ") and match_team(c["libelle"][len("Victoire "):], [equipe]):
            out.append(c)
        elif c["libelle"].startswith("Plus de"):
            out.append(c)
    return out


def cote_actuelle(ev, libelle):
    """La cote Betclic actuelle d'une sélection, dans un événement The Odds API déjà lu."""
    if ev is None:
        return None
    bc = ev["betclic"]
    if libelle == "Match nul":
        return bc["h2h"].get("D")
    if libelle.startswith("Victoire "):
        nom = libelle[len("Victoire "):]
        return bc["h2h"].get("H") if nom == ev["home"] else bc["h2h"].get("A") if nom == ev["away"] else None
    mo = re.match(r"(Plus|Moins) de ([0-9,]+) ", libelle)
    if mo:
        ligne = float(mo.group(2).replace(",", "."))
        return bc["totals"].get(ligne, {}).get("Over" if mo.group(1) == "Plus" else "Under")
    return None


def bandeau_compos(statuts, matchs, now):
    """Encadré « Compos et absences » placé en haut de la page téléphone."""
    lignes = []
    for mid, st in sorted(statuts.items(), key=lambda kv: matchs.get(kv[0], {}).get("start", "")):
        info = matchs.get(mid)
        if not info or not (st.get("compo") or st.get("absents_nouveaux")):
            continue
        debut = datetime.fromisoformat(info["start"])
        if debut < now - timedelta(hours=3):
            continue
        txt = []
        for x in st.get("absents_nouveaux", []):
            txt.append(f'<span style="color:#C1121F;font-weight:600">Absent : {e(x)}</span>')
        compo = st.get("compo") or {}
        for cote in ("home", "away"):
            for j in compo.get(cote, []):
                if j["etat"] != "titulaire":
                    txt.append(f'<span style="color:#C1121F;font-weight:600">{e(j["nom"])} {e(j["etat"])}</span>')
        if compo and not any(j["etat"] != "titulaire" for c in ("home", "away") for j in compo.get(c, [])):
            txt.append('<span style="color:#18181B">Compo officielle : tous les joueurs clés sont titulaires</span>')
        lignes.append(f'<div style="padding:10px 0;border-top:1px solid #E4E4E7">'
                      f'<div style="font-size:13px;color:#52525B">{e(info["home"])} – {e(info["away"])}, {heure(debut)}</div>'
                      f'<div style="font-size:15px;margin-top:3px">{" · ".join(txt)}</div></div>')
    if not lignes:
        return ""
    return (f'<div style="border:1px solid #E4E4E7;border-left:4px solid #C1121F;border-radius:12px;padding:12px 16px 6px;'
            f'margin:0 0 16px;background:#fff">'
            f'<div style="font:700 20px/1.2 \'Barlow Semi Condensed\',\'Arial Narrow\',sans-serif">Compos et absences</div>'
            f'<div style="font-size:13px;color:#52525B;margin-bottom:8px">Mis à jour le {datetime.now(TZ):%d/%m à %H:%M}</div>'
            + "".join(lignes) + "</div>")


def email_alertes(alertes) -> str:
    cartes = []
    for a in alertes:
        touches = "".join(
            f'<li style="margin:4px 0"><b>{e(c["libelle"])}</b> <span style="color:#5f6b7a">({e(c["groupe"])})</span>'
            + (f' · cote actuelle <b>{fr(c["cote_actuelle"])}</b>' if c.get("cote_actuelle") else "") + "</li>"
            for c in a["touches"])
        cartes.append(
            f'<div style="border:1px solid #e3e7ec;border-radius:12px;padding:16px;margin:12px 0;background:#fff">'
            f'<div style="font-size:14px;color:#5f6b7a">{e(a["match"])} · {e(a["quand"])}</div>'
            f'<div style="font-size:20px;font-weight:800;color:#b42318;margin:4px 0">{e(a["titre"])}</div>'
            + (f'<div style="font-size:15px;margin-top:6px">Tes conseils touchés :</div><ul style="font-size:15px;padding-left:20px;margin:6px 0">{touches}</ul>'
               if touches else '<div style="font-size:15px;margin-top:6px">Aucun de tes conseils n\'est directement touché.</div>')
            + "</div>")
    return (f'<!doctype html><html lang="fr"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1"></head>'
            f'<body style="margin:0;background:#f5f7fa;font-family:-apple-system,\'Segoe UI\',Roboto,Arial,sans-serif;color:#1f2328">'
            f'<div style="max-width:600px;margin:0 auto;padding:20px 14px">'
            f'<div style="font-size:26px;font-weight:800">Changement avant match</div>'
            f'<div style="font-size:15px;color:#5f6b7a;margin-top:4px">Vérifie tes paris avant le coup d\'envoi.</div>'
            + "".join(cartes)
            + '<div style="font-size:13px;color:#5f6b7a;margin-top:20px">Ne mise que ce que tu peux perdre. '
              'Joueurs Info Service : 09 74 75 13 13.</div></div></body></html>')


def avant_match(now, dry_run=False):
    data = _lire_json(F_CONSEILS, None)
    if not data or not data.get("matchs"):
        log("Aucun bilan enregistré : rien à surveiller (le prochain bilan créera la liste)")
        return
    echecs = []
    api = APIFoot(echecs)
    if not api.ok:
        log("API_FOOTBALL_KEY absente : contrôle des compos impossible")
        return
    matchs, conseils = data["matchs"], data["conseils"]
    statuts = _lire_json(F_STATUTS, {})
    deja = set(_lire_json(F_ALERTES, []))
    aujourd_hui = now.astimezone(TZ).strftime("%Y-%m-%d")
    alertes, change = [], False
    fpl = None

    for mid, info in matchs.items():
        debut = datetime.fromisoformat(info["start"])
        reste_min = (debut - now).total_seconds() / 60
        if reste_min < -10 or reste_min > FENETRE_BLESSURES_H * 60:
            continue
        st = statuts.setdefault(mid, {})
        ligue = LIGUES_APIFOOT.get(info.get("comp_id"))
        if not ligue:
            continue
        if not info.get("fixture_id"):
            fx = api.trouver_match(ligue, info["home"], info["away"], debut, now)
            if not fx:
                continue
            info["fixture_id"] = fx["fixture"]["id"]
        match_txt, quand = f'{info["home"]} – {info["away"]}', heure(debut)
        cles = info.get("cles") or {"home": [], "away": []}

        def signaler(joueur, cote_eq, titre, cle):
            if cle in deja:
                return
            deja.add(cle)
            alertes.append({"match_id": mid, "match": match_txt, "quand": quand, "titre": titre,
                            "touches": conseils_touches(conseils, mid, joueur, cote_eq, info),
                            "comp_id": info.get("comp_id")})

        # 1) blessures et suspensions : une fois par jour, pour les matchs des 48 h à venir
        if st.get("blessures_jour") != aujourd_hui:
            st["blessures_jour"], change = aujourd_hui, True
            absents = []
            for b in api.blessures(ligue, debut.astimezone(timezone.utc).strftime("%Y-%m-%d"), now):
                if (b.get("fixture") or {}).get("id") == info["fixture_id"] and b["player"].get("type") == "Missing Fixture":
                    cote_eq = "home" if match_team(info["home"], [b["team"]["name"]]) else "away"
                    absents.append((b["player"]["name"], cote_eq, b["player"].get("reason") or "absent"))
            if info.get("comp_id") == "soccer_epl":
                fpl = fpl if fpl is not None else fpl_joueurs()
                if fpl is not None:
                    for cote_eq in ("home", "away"):
                        t = match_team(info[cote_eq], fpl["team"].unique().tolist())
                        for r in (fpl[fpl["team"] == t].itertuples() if t else []):
                            ch = None if pd.isna(r.chance) else int(r.chance)
                            if r.statut in ("i", "s", "u") or (ch is not None and ch <= 25):
                                absents.append((f"{r.joueur} / {r.court}" if r.court else r.joueur, cote_eq,
                                                r.news or "absent"))
            for nom, cote_eq, raison in absents:
                if dans_liste(nom, cles.get(cote_eq, [])) and not dans_liste(nom, info.get("absents_connus", [])):
                    st.setdefault("absents_nouveaux", [])
                    if not dans_liste(nom, st["absents_nouveaux"]):
                        st["absents_nouveaux"].append(nom_affiche(nom))
                    signaler(nom, cote_eq, f"{nom_affiche(nom)} ({info[cote_eq]}) absent : {raison}",
                             f"{mid}|{norm(nom_affiche(nom))}|absent")

        # 2) compo officielle : dans les 75 minutes avant le coup d'envoi
        if -10 <= reste_min <= FENETRE_COMPO_MIN and not st.get("compo"):
            lu = api.compos(info["fixture_id"])
            if len(lu) >= 2:
                compo = {}
                for equipe in lu:
                    cote_eq = "home" if match_team(info["home"], [equipe["team"]["name"]]) else "away"
                    xi = [p["player"]["name"] for p in equipe.get("startXI", [])]
                    rempl = [p["player"]["name"] for p in equipe.get("substitutes", [])]
                    compo[cote_eq] = []
                    etats = [("titulaire" if dans_liste(nom, xi) else "remplaçant" if dans_liste(nom, rempl)
                              else "absent du groupe") for nom in cles.get(cote_eq, [])]
                    # garde-fou : aucun joueur clé reconnu dans toute la feuille de match = noms mal reconnus,
                    # pas une hécatombe ; on n'alerte pas sur une erreur de lecture
                    noms_ok = len(xi) >= 11 and any(x != "absent du groupe" for x in etats) or len(etats) == 0
                    if not noms_ok and len(xi) >= 11:
                        log(f"   {info[cote_eq]} : joueurs clés introuvables dans la compo (noms ?), pas d'alerte")
                        st["noms_non_reconnus"] = True
                    for nom, etat in zip(cles.get(cote_eq, []), etats):
                        compo[cote_eq].append({"nom": nom_affiche(nom), "etat": etat})
                        if etat != "titulaire" and (noms_ok or etat == "remplaçant"):
                            signaler(nom, cote_eq, f"{nom_affiche(nom)} ({info[cote_eq]}) {etat}",
                                     f"{mid}|{norm(nom_affiche(nom))}|{etat}")
                st["compo"], change = compo, True
                log(f"   Compo reçue : {match_txt}")
            else:
                log(f"   Compo pas encore publiée : {match_txt}")

    # 3) cotes actuelles des conseils touchés (2 crédits par championnat, seulement s'il y a une alerte)
    if alertes and ODDS_API_KEY:
        src = SourcesReelles(use_llm=False)
        evs = {}
        for cid in {a["comp_id"] for a in alertes if a.get("comp_id")}:
            comp = next((c for c in COMPETITIONS if c["id"] == cid), None)
            for ev in (src.cotes(comp) if comp else []):
                evs[str(ev["id"])] = ev
        for a in alertes:
            for c in a["touches"]:
                if c["type"] != "buteur":
                    c["cote_actuelle"] = cote_actuelle(evs.get(a["match_id"]), c["libelle"])

    data["matchs"] = matchs
    _ecrire_json(F_CONSEILS, data)
    _ecrire_json(F_STATUTS, statuts)
    _ecrire_json(F_ALERTES, sorted(deja))
    log(f"Contrôle terminé : {len(alertes)} nouvelle(s) alerte(s), {api._compteur()} requête(s) API-Football aujourd'hui")
    for x in echecs:
        log(f"   {x}")

    # page téléphone : le bilan de la semaine + l'encadré des compos, seulement s'il y a du nouveau
    page_dir, base = os.environ.get("PAGE_DIR"), CACHE_DIR / "site_base"
    if page_dir and change and (base / "index.html").exists():
        import shutil
        d = Path(page_dir)
        if d.exists():
            shutil.rmtree(d)
        shutil.copytree(base, d)
        index = (d / "index.html").read_text(encoding="utf-8")
        (d / "index.html").write_text(index.replace("<!--COMPOS-->", bandeau_compos(statuts, matchs, now), 1),
                                      encoding="utf-8")
        log("   Page téléphone mise à jour")

    if not alertes:
        return
    OUT_DIR.mkdir(exist_ok=True)
    html_mail = email_alertes(alertes)
    (OUT_DIR / f"alerte_{now.astimezone(TZ):%Y%m%d_%H%M}.html").write_text(html_mail, encoding="utf-8")
    if dry_run or not (GMAIL_USER and GMAIL_APP_PASSWORD):
        log("Alerte écrite dans rapports/ (pas d'envoi : --dry-run ou identifiants Gmail absents)")
        return
    sujet = "Compo : " + alertes[0]["titre"] + (f" (+{len(alertes) - 1} autre(s))" if len(alertes) > 1 else "")
    envoyer_email(html_mail, sujet[:150], None)
    log("E-mail d'alerte envoyé")


# =============================================================================
# MAIN
# =============================================================================
def main():
    ap = argparse.ArgumentParser(description="Rapport Betclic hebdomadaire")
    ap.add_argument("--demo", action="store_true", help="données simulées, hors ligne, sans e-mail")
    ap.add_argument("--dry-run", action="store_true", help="vraies données, sans e-mail")
    ap.add_argument("--no-llm", action="store_true", help="désactive les actus Gemini")
    ap.add_argument("--avant-match", action="store_true",
                    help="contrôle léger : compos officielles et blessures des matchs conseillés")
    ap.add_argument("--jours", type=float, default=float((os.environ.get("FENETRE_JOURS") or "4.5").replace(",", ".")))
    args = ap.parse_args()

    if args.avant_match:
        avant_match(datetime.now(timezone.utc), dry_run=args.dry_run)
        return
    src = SourcesDemo() if args.demo else SourcesReelles(use_llm=not args.no_llm)
    now = src.now if args.demo else datetime.now(timezone.utc)
    fin = now + timedelta(days=args.jours)

    log("1/4 Cotes Betclic + Pinnacle (marchés vainqueur et nombre de buts)")
    evenements, src.perimetre = {}, []
    for comp in COMPETITIONS:
        if comp["id"].startswith(SPORTS_INTERDITS):
            log(f"   {comp['nom']} : exclu (Italie)")
            continue
        brut = [ev for ev in src.cotes(comp) if now <= ev["start"] <= fin and ev["betclic"]["h2h"]]
        if comp.get("ldc") and EXCLURE_ITALIENS_LDC:
            brut = [ev for ev in brut if not (est_italien(ev["home"]) or est_italien(ev["away"]))]
        clubs, txt = perimetre(comp, src, now) if comp["cat"] == "FOOT" else (None, "tous les matchs")
        evs = [ev for ev in brut if garder_match(ev, clubs)]
        src.perimetre.append((comp["nom"], txt))
        log(f"   {comp['nom']} : {len(evs)} match(s) retenu(s) sur {len(brut)} · {txt}")
        if evs:
            evenements[comp["id"]] = (comp, evs)

    log("2/4 Modèles et probabilités")
    blessures = src.blessures_nba() if any(c.get("nba") for c, _ in evenements.values()) else {}
    matchs_f, matchs_b = [], []
    for comp, evs in evenements.values():
        try:
            res = analyser_foot(comp, evs, src, now) if comp["cat"] == "FOOT" else analyser_nba(comp, evs, src, now, blessures)
        except Exception as ex:
            log(f"   {comp['nom']} : analyse impossible ({ex})")
            src.echecs.append(f"Analyse {comp['nom']} : {ex}")
            continue
        (matchs_f if comp["cat"] == "FOOT" else matchs_b).extend(res)
        log(f"   {comp['nom']} : ok")

    if matchs_f and not args.demo:
        log("   Effectifs : blessures, suspensions et joueurs clés (API-Football, Fantasy Premier League)")
        try:
            enrichir_effectifs(matchs_f, src, now)
        except Exception as ex:
            log(f"   Effectifs indisponibles ({ex})")
            src.echecs.append(f"Effectifs : {ex}")

    log("3/4 Actus blessés (facultatif, matchs à sélection intéressante seulement)")
    def interet(m):
        return max([o["edge"] + (0.05 if o["p"] >= 0.6 else 0) for o in m["options"]] or [-1])
    cibles = sorted([m for m in matchs_f + matchs_b if interet(m) > -0.03], key=interet, reverse=True)[:ACTUS_MAX_MATCHS]
    actus = src.actus([{"id": m["id"], "home": m["home"], "away": m["away"]} for m in cibles], now)
    for m in matchs_f + matchs_b:
        a = actus.get(str(m["id"]))
        if a and a["alerte"] and a["resume"]:
            m["alerte"] = (m["alerte"] + " · " if m.get("alerte") else "") + a["resume"]
        if m.get("alerte"):
            for o in m["options"]:
                o["alerte"] = m["alerte"]

    log("4/4 Rapport, e-mail et PDF")
    page, _ = generer_html(matchs_f, matchs_b, src, now, fin)
    OUT_DIR.mkdir(exist_ok=True)
    base = "demo" if args.demo else f"{now.astimezone(TZ):%Y%m%d_%H%M}"
    (OUT_DIR / f"rapport_{base}.html").write_text(page, encoding="utf-8")
    syn = synthese(matchs_f, matchs_b)
    log("   Joueurs en forme et pépites")
    syn["joueurs"] = joueurs_semaine(src, matchs_f, matchs_b, now)
    if not args.demo:
        sauver_conseils(matchs_f, syn, now)
    pdf = OUT_DIR / f"Bilan_Betclic_{now.astimezone(TZ):%d-%m-%Y}{'_demo' if args.demo else ''}.pdf"
    pdf_ok = generer_pdf(pdf, matchs_f, matchs_b, syn, src, now, fin)
    mail = generer_email(matchs_f, matchs_b, syn, src, now, fin, avec_pdf=pdf_ok)
    (OUT_DIR / f"email_{base}.html").write_text(mail, encoding="utf-8")
    page_dir = os.environ.get("PAGE_DIR")
    if page_dir:                       # version « appli » pour le téléphone (publiée par GitHub Pages)
        import shutil
        d = Path(page_dir)
        d.mkdir(parents=True, exist_ok=True)
        (d / "index.html").write_text(generer_email(matchs_f, matchs_b, syn, src, now, fin, avec_pdf=pdf_ok, page=True),
                                      encoding="utf-8")
        (d / "detail.html").write_text(page, encoding="utf-8")
        if pdf_ok:
            shutil.copy(pdf, d / "bilan.pdf")
        ecrire_icone(d)
        if not args.demo:                       # repris par les contrôles avant-match de la semaine
            base_site = CACHE_DIR / "site_base"
            if base_site.exists():
                shutil.rmtree(base_site)
            shutil.copytree(d, base_site)
        log(f"   Page téléphone écrite dans : {d.resolve()}")
    log(f"   Fichiers écrits dans : {OUT_DIR.resolve()}")
    log(f"   PDF : {pdf.name if pdf_ok else 'non généré'}  ·  aperçu du mail : email_{base}.html")
    if not args.demo:
        archiver(matchs_f + matchs_b, now)
    if args.demo or args.dry_run:
        log("Pas d'envoi d'e-mail (mode démo ou --dry-run)")
        return
    if not (GMAIL_USER and GMAIL_APP_PASSWORD):
        log("GMAIL_USER / GMAIL_APP_PASSWORD absents : e-mail non envoyé")
        return
    n = len(syn["a_jouer"])
    sujet = (f"Tes paris du {now.astimezone(TZ):%d/%m} : {n} pari{'s' if n > 1 else ''} à jouer" if n
             else f"Tes paris du {now.astimezone(TZ):%d/%m} : rien d'intéressant cette semaine")
    envoyer_email(mail, sujet, pdf if pdf_ok else None)
    log("E-mail envoyé")


if __name__ == "__main__":
    main()
