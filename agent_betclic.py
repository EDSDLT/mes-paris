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


def cached_bytes(url: str, name: str, max_age_h: float = 12):
    CACHE_DIR.mkdir(exist_ok=True)
    f = CACHE_DIR / name
    if f.exists() and (time.time() - f.stat().st_mtime) < max_age_h * 3600:
        return f.read_bytes()
    r = http_get(url)
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
        res = pd.read_csv(f_res) if f_res.exists() else pd.DataFrame(columns=["jour", "home", "away", "hpts", "apts"])
        faits = set(f_jours.read_text().split()) if f_jours.exists() else set()
        hier = now.astimezone(TZ).date() - timedelta(days=1)
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
                                     "hpts": int(float(eq["home"]["score"])), "apts": int(float(eq["away"]["score"]))})
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


def _combo(legs, nom=""):
    legs = tuple(legs)
    cote = math.prod(o["cote"] for o in legs)
    p = math.prod(o["p"] for o in legs)
    return {"nom": nom, "legs": legs, "cote": cote, "p": p, "ev": p * cote - 1}


def _chercher(cands, kmin, kmax, cmin, cmax, n=2, critere=lambda c: -c["p"]):
    """Les n meilleurs combinés (une sélection par match), sans sélection en commun entre eux."""
    cands = sorted(cands, key=lambda o: -o["p"])[:14]
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
    res = {
        "safe": _chercher([o for o in pool if o["p"] >= 0.60], 2, 4, 2.00, 2.50),
        "difficile": _chercher([o for o in pool if o["p"] >= 0.50], 3, 5, 3.60, 4.50,
                               critere=lambda c: (-c["p"], abs(c["cote"] - 4))),
        "global": None, "ldc": [],
    }
    foot = sorted([m for m in matchs if m["cat"] == "FOOT"], key=lambda m: m["start"])
    legs = [l for l in (_plus_probable(m) for m in foot) if l]
    if len(legs) >= 2:
        res["global"] = _combo(legs, f"Tous les matchs de la sélection ({len(legs)})")

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
        fav = [l for l in (_plus_probable(m, lambda o: o["marche"] == "1N2" and o["libelle"].startswith("Victoire")
                                          and o["p"] >= 0.55) for m in ms) if l]
        if len(fav) >= 2:
            props.append(_combo(fav, "Les favoris de la soirée"))
        buts = [l for l in (_plus_probable(m, lambda o: o["marche"] == "Buts") for m in ms) if l]
        if len(buts) >= 2:
            props.append(_combo(buts, "Les buts de la soirée"))
        obj4 = _chercher(nuit, 2, 4, 3.50, 4.60, n=1, critere=lambda c: (-c["p"], abs(c["cote"] - 4)))
        if obj4:
            props.append({**obj4[0], "nom": "Objectif cote 4"})
        tous = [l for l in (_plus_probable(m) for m in ms) if l]
        if len(tous) >= 2:
            props.append(_combo(tous, f"Tous les matchs de la soirée ({len(tous)})"))
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
         ("Paris plus difficiles", "Davantage de sélections pour une cote totale autour de 4,00.", comb["difficile"])]
    if comb["global"]:
        g.append(("Combiné global", "Une sélection par match (la plus probable) sur tous les matchs retenus. "
                  "Très peu de chances de passer : pour le plaisir.", [comb["global"]]))
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
    return {"SOLIDE": pill("SOLIDE", C["rouge"], C["rouge_f"]), "MOYEN": pill("MOYEN", C["ambre"], C["ambre_f"]),
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
        f'<div style="font-size:18px;font-weight:800">{e(b["joueur"])}</div>'
        f'<div style="font-size:14px;color:{gris}">{e(b["equipe"])} contre {e(b["adv"])} · {heure(b["start"])}</div>'
        f'<div style="font-size:16px;margin-top:8px">Chance de marquer : <b>{pc(b["p"])}</b></div>'
        f'<div style="font-size:15px;margin-top:4px">Joue-le seulement si Betclic le cote <b>au moins {fr(b["cote_min"] * 1.1)}</b></div></div>'
        for b in buteurs)

    if page:
        bouton = ('<a href="{}" style="display:block;text-align:center;background:#1a56db;color:#fff;'
                  'text-decoration:none;font-weight:700;font-size:17px;padding:14px;border-radius:10px;margin:8px 0">{}</a>')
        pdf_txt = ((bouton.format("bilan.pdf", "Ouvrir le PDF détaillé") if avec_pdf else "")
                   + bouton.format("detail.html", "Voir toutes les stats des matchs")
                   + f'<div style="font-size:13px;color:{gris};text-align:center;margin-top:6px">'
                     f'Mis à jour le {datetime.now(TZ):%d/%m/%Y à %H:%M}</div>')
    else:
        pdf_txt = ("Tout le détail (stats de chaque équipe, tous les matchs, autres buteurs) est dans le "
                   "<b>PDF joint</b> à ce mail." if avec_pdf else "")
    corps = (
        f'<div style="font-size:28px;font-weight:800;line-height:1.2">Tes paris de la semaine</div>'
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
# MAIN
# =============================================================================
def main():
    ap = argparse.ArgumentParser(description="Rapport Betclic hebdomadaire")
    ap.add_argument("--demo", action="store_true", help="données simulées, hors ligne, sans e-mail")
    ap.add_argument("--dry-run", action="store_true", help="vraies données, sans e-mail")
    ap.add_argument("--no-llm", action="store_true", help="désactive les actus Gemini")
    ap.add_argument("--jours", type=float, default=float((os.environ.get("FENETRE_JOURS") or "4.5").replace(",", ".")))
    args = ap.parse_args()

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
