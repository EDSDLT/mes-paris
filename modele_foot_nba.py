#!/usr/bin/env python3
"""
modele_foot_nba.py : modèle de référence, 100 % gratuit, volontairement lisible.

Contenu
  1. DixonColes   : modèle de buts football (Poisson corrigé, pondéré par le temps)
  2. markets()    : 1X2, over/under, BTTS et combinés d'un même match
  3. devig_*()    : retrait de la marge du bookmaker
  4. métriques    : log loss, Brier, RPS
  5. walk_forward : backtest sans fuite de données
  6. NBAElo       : Elo avec marge de victoire
  7. selftest()   : test sur données simulées (paramètres connus)

Usage
  python modele_foot_nba.py --selftest
  python modele_foot_nba.py --backtest E0 2021 2022 2023 2024    (internet requis)

Dépendances : numpy pandas scipy
"""
import argparse

import numpy as np
import pandas as pd
from scipy.optimize import brentq, minimize
from scipy.special import gammaln

MAXG = 10  # grille de scores : 0..10 buts par équipe


# ----------------------------------------------------------------------------
# 1. DIXON-COLES
# ----------------------------------------------------------------------------
def score_grid(lam, mu, rho):
    """Matrice P[i, j] = P(domicile marque i, extérieur marque j).

    Poisson indépendants, puis correction de Dixon-Coles sur 0-0, 0-1, 1-0, 1-1.
    """
    g = np.arange(MAXG + 1)
    ph = np.exp(g * np.log(lam) - lam - gammaln(g + 1))
    pa = np.exp(g * np.log(mu) - mu - gammaln(g + 1))
    P = np.outer(ph, pa)
    P[0, 0] *= 1 - lam * mu * rho
    P[0, 1] *= 1 + lam * rho
    P[1, 0] *= 1 + mu * rho
    P[1, 1] *= 1 - rho
    return P / P.sum()  # renormalise la queue tronquée (> 10 buts)


class DixonColes:
    """log(lam_dom) = avantage_dom + attaque[dom] - defense[ext]
       log(mu_ext) = attaque[ext] - defense[dom]
    defense élevée = défense solide. Moyennes recentrées à 0 (identifiabilité).
    Chaque match pèse exp(-xi * jours_depuis_le_match) : le récent compte plus.
    """

    def __init__(self, xi=0.0019, l2=1.0):
        self.xi, self.l2 = xi, l2  # xi : décroissance/jour ; l2 : régularisation

    def fit(self, df, ref_date=None):
        """df : colonnes date (datetime), home, away, hg, ag."""
        self.teams = sorted(set(df.home) | set(df.away))
        n = len(self.teams)
        idx = {t: i for i, t in enumerate(self.teams)}
        h = df.home.map(idx).to_numpy()
        a = df.away.map(idx).to_numpy()
        x = df.hg.to_numpy(float)
        y = df.ag.to_numpy(float)
        ref = pd.Timestamp(ref_date) if ref_date is not None else df.date.max()
        age = (ref - df.date).dt.days.clip(lower=0).to_numpy(float)
        w = np.exp(-self.xi * age)
        const = gammaln(x + 1) + gammaln(y + 1)

        def unpack(p):
            att, dfn = p[:n], p[n:2 * n]
            return att - att.mean(), dfn - dfn.mean(), p[2 * n], p[2 * n + 1]

        def nll(p):
            att, dfn, ha, rho = unpack(p)
            eh = ha + att[h] - dfn[a]
            ea = att[a] - dfn[h]
            lam, mu = np.exp(eh), np.exp(ea)
            t = np.ones_like(lam)
            m = (x == 0) & (y == 0); t[m] = 1 - lam[m] * mu[m] * rho
            m = (x == 0) & (y == 1); t[m] = 1 + lam[m] * rho
            m = (x == 1) & (y == 0); t[m] = 1 + mu[m] * rho
            m = (x == 1) & (y == 1); t[m] = 1 - rho
            if (t <= 0).any():
                return 1e12
            ll = np.log(t) + x * eh - lam + y * ea - mu - const
            return -(w * ll).sum() + self.l2 * (att @ att + dfn @ dfn)

        p0 = np.zeros(2 * n + 2)
        p0[2 * n] = 0.25
        bounds = [(-3, 3)] * (2 * n) + [(-1, 1), (-0.3, 0.3)]
        res = minimize(nll, p0, method="L-BFGS-B", bounds=bounds)
        self.att, self.dfn, self.home, self.rho = unpack(res.x)
        self.converged = bool(res.success)
        self.unseen = set()
        return self

    def _strength(self, team):
        if team in self.teams:
            i = self.teams.index(team)
            return self.att[i], self.dfn[i]
        self.unseen.add(team)  # équipe inconnue (promue...) : niveau moyen
        return 0.0, 0.0

    def grid(self, home, away):
        ah, dh = self._strength(home)
        aa, da = self._strength(away)
        lam = np.exp(self.home + ah - da)
        mu = np.exp(aa - dh)
        return score_grid(lam, mu, self.rho), lam, mu


# ----------------------------------------------------------------------------
# 2. MARCHÉS (tout sort de la même matrice de scores)
# ----------------------------------------------------------------------------
def markets(P, line=2.5):
    i, j = np.indices(P.shape)
    tot = i + j
    return {
        "H": P[i > j].sum(), "D": P[i == j].sum(), "A": P[i < j].sum(),
        "over": P[tot > line].sum(), "under": P[tot < line].sum(),
        "btts": P[(i > 0) & (j > 0)].sum(),
        # combinés d'un MÊME match : la corrélation est gérée par la matrice
        "H&over": P[(i > j) & (tot > line)].sum(),
        "H&btts": P[(i > j) & (i > 0) & (j > 0)].sum(),
    }


# ----------------------------------------------------------------------------
# 3. RETRAIT DE LA MARGE
# ----------------------------------------------------------------------------
def devig_prop(odds):
    q = 1 / np.asarray(odds, float)
    return q / q.sum()


def devig_power(odds):
    """Cherche k tel que sum((1/cote)^k) = 1. Retire plus de marge sur les outsiders."""
    q = 1 / np.asarray(odds, float)
    k = brentq(lambda k: (q ** k).sum() - 1, 1.0, 20.0)
    return q ** k


# ----------------------------------------------------------------------------
# 4. MÉTRIQUES (P : N x 3 en ordre H, D, A ; o : 0=H, 1=D, 2=A)
# ----------------------------------------------------------------------------
def log_loss(P, o):
    return -np.mean(np.log(np.clip(P[np.arange(len(P)), o], 1e-12, 1)))


def brier(P, o):
    return np.mean(((P - np.eye(3)[o]) ** 2).sum(1))


def rps(P, o):
    cp = np.cumsum(P, 1)[:, :-1]
    co = np.cumsum(np.eye(3)[o], 1)[:, :-1]
    return np.mean(((cp - co) ** 2).sum(1) / 2)


def outcome_idx(hg, ag):
    return np.where(hg > ag, 0, np.where(hg == ag, 1, 2))


# ----------------------------------------------------------------------------
# 5. BACKTEST WALK-FORWARD (le modèle ne voit jamais le futur)
# ----------------------------------------------------------------------------
def walk_forward(df, first_test_date, step_days=28, min_train=300, **kw):
    df = df.sort_values("date").reset_index(drop=True)
    rows, t0, end = [], pd.Timestamp(first_test_date), df.date.max()
    while t0 <= end:
        t1 = t0 + pd.Timedelta(days=step_days)
        train = df[df.date < t0]
        test = df[(df.date >= t0) & (df.date < t1)]
        if len(train) >= min_train and len(test):
            m = DixonColes(**kw).fit(train, ref_date=t0)
            for r in test.itertuples():
                mk = markets(m.grid(r.home, r.away)[0])
                rows.append((r.Index, mk["H"], mk["D"], mk["A"], mk["over"]))
        t0 = t1
    res = pd.DataFrame(rows, columns=["i", "pH", "pD", "pA", "pOver"]).set_index("i")
    return df.join(res, how="inner")


# ----------------------------------------------------------------------------
# 6. NBA : ELO AVEC MARGE DE VICTOIRE
# ----------------------------------------------------------------------------
class NBAElo:
    def __init__(self, k=20, home_adv=100, mean=1505, carry=0.75):
        self.k, self.ha, self.mean, self.carry = k, home_adv, mean, carry
        self.r = {}

    def rating(self, t):
        return self.r.get(t, self.mean)

    def p_home(self, home, away):
        d = self.rating(home) + self.ha - self.rating(away)
        return 1 / (1 + 10 ** (-d / 400))

    def update(self, home, away, hpts, apts):
        """Renvoie la proba AVANT match, puis met à jour les ratings."""
        d = self.rating(home) + self.ha - self.rating(away)
        p = 1 / (1 + 10 ** (-d / 400))
        won = hpts > apts
        win_d = d if won else -d
        mult = (abs(hpts - apts) + 3) ** 0.8 / (7.5 + 0.006 * win_d)
        delta = self.k * mult * (float(won) - p)
        self.r[home] = self.rating(home) + delta
        self.r[away] = self.rating(away) - delta
        return p

    def new_season(self):
        for t in self.r:
            self.r[t] = self.carry * self.r[t] + (1 - self.carry) * self.mean


# ----------------------------------------------------------------------------
# 7. TESTS SUR DONNÉES SIMULÉES
# ----------------------------------------------------------------------------
def _simulate_league(rng, n_teams=20, seasons=3, home=0.25, rho=-0.08, sd=0.25):
    att = rng.normal(0, sd, n_teams); att -= att.mean()
    dfn = rng.normal(0, sd, n_teams); dfn -= dfn.mean()
    rows, start = [], pd.Timestamp("2021-08-01")
    pairs = [(i, j) for i in range(n_teams) for j in range(n_teams) if i != j]
    for s in range(seasons):
        order = rng.permutation(len(pairs))
        for k, pi in enumerate(order):
            i, j = pairs[pi]
            lam = np.exp(home + att[i] - dfn[j])
            mu = np.exp(att[j] - dfn[i])
            P = score_grid(lam, mu, rho)
            hg, ag = divmod(rng.choice(P.size, p=P.ravel()), P.shape[1])
            day = start + pd.Timedelta(days=365 * s + int(k * 300 / len(pairs)))
            rows.append((day, f"T{i:02d}", f"T{j:02d}", hg, ag))
    df = pd.DataFrame(rows, columns=["date", "home", "away", "hg", "ag"])
    return df, att, dfn, home, rho


def selftest(seed=7):
    from scipy.stats import norm, poisson

    rng = np.random.default_rng(seed)
    print("=== TEST 1 : formules ===")
    P0 = score_grid(1.4, 1.1, 0.0)
    ref = np.outer(poisson.pmf(np.arange(MAXG + 1), 1.4), poisson.pmf(np.arange(MAXG + 1), 1.1))
    print(f"rho=0 : écart max avec Poisson scipy = {np.abs(P0 - ref / ref.sum()).max():.2e} (attendu ~0)")
    mk = markets(score_grid(1.6, 1.0, -0.08))
    print(f"H+D+A = {mk['H'] + mk['D'] + mk['A']:.6f} (attendu 1) | over+under = {mk['over'] + mk['under']:.6f}")
    print(f"P(H&over)={mk['H&over']:.3f} vs P(H)*P(over)={mk['H'] * mk['over']:.3f} "
          "(différents : c'est la corrélation)")
    q = [2.10, 3.40, 3.60]
    print(f"démarginage 2.10/3.40/3.60 : proportionnel={devig_prop(q).round(3)} "
          f"puissance={devig_power(q).round(3)} (somme=1)")

    print("\n=== TEST 2 : récupération des paramètres (3 saisons simulées) ===")
    df, att, dfn, home, rho = _simulate_league(rng)
    train = df[df.date < "2023-08-01"]
    test = df[df.date >= "2023-08-01"].reset_index(drop=True)
    m = DixonColes(xi=0.0, l2=1.0).fit(train)
    print(f"convergence : {m.converged} | {len(train)} matchs d'entraînement")
    print(f"corrélation attaque estimée/vraie : {np.corrcoef(m.att, att)[0, 1]:.3f}")
    print(f"corrélation défense estimée/vraie : {np.corrcoef(m.dfn, dfn)[0, 1]:.3f}")
    print(f"avantage domicile : estimé {m.home:.3f} / vrai {home:.3f}")
    print(f"rho : estimé {m.rho:.3f} / vrai {rho:.3f} (le plus bruité des paramètres : il varie selon la graine)")

    print("\n=== TEST 3 : qualité des probabilités sur la saison non vue ===")
    PM, PT = [], []
    for r in test.itertuples():
        i, j = int(r.home[1:]), int(r.away[1:])
        a = markets(m.grid(r.home, r.away)[0])
        t = markets(score_grid(np.exp(home + att[i] - dfn[j]), np.exp(att[j] - dfn[i]), rho))
        PM.append([a["H"], a["D"], a["A"]])
        PT.append([t["H"], t["D"], t["A"]])
    PM, PT = np.array(PM), np.array(PT)
    o = outcome_idx(test.hg.to_numpy(), test.ag.to_numpy())
    freq = np.bincount(outcome_idx(train.hg.to_numpy(), train.ag.to_numpy()), minlength=3) / len(train)
    PB = np.tile(freq, (len(test), 1))
    print(f"{'':28s}{'log loss':>10s}{'Brier':>9s}{'RPS':>9s}")
    for name, P in [("fréquences brutes", PB), ("modèle ajusté", PM), ("vrais paramètres (plafond)", PT)]:
        print(f"{name:28s}{log_loss(P, o):10.4f}{brier(P, o):9.4f}{rps(P, o):9.4f}")
    print(f"écart moyen |p modèle - p vraie| : {np.abs(PM - PT).mean():.4f}")

    print("\n=== TEST 4 : calibration (proba domicile) ===")
    bins = np.array([0, .3, .4, .5, .6, .7, 1.0])
    k = np.digitize(PM[:, 0], bins) - 1
    print(f"{'tranche':>12s}{'n':>6s}{'proba prédite':>15s}{'fréq. réelle':>14s}")
    for b in range(len(bins) - 1):
        s = k == b
        if s.sum() >= 5:
            print(f"{bins[b]:.1f}-{bins[b + 1]:.1f}{s.sum():>8d}{PM[s, 0].mean():>15.3f}{(o[s] == 0).mean():>14.3f}")

    print("\n=== TEST 5 : Elo NBA (30 équipes, 3 saisons simulées) ===")
    teams = [f"N{i:02d}" for i in range(30)]
    strength = rng.normal(0, 4.5, 30)  # points de différence
    elo, probs, res_, truep = NBAElo(), [], [], []
    for s in range(3):
        for _ in range(1230):
            i, j = rng.choice(30, 2, replace=False)
            diff = strength[i] - strength[j] + 3.0 + rng.normal(0, 12)
            hp, ap = 105 + diff / 2, 105 - diff / 2
            p = elo.update(teams[i], teams[j], hp, ap)
            if s >= 1:
                probs.append(p)
                res_.append(float(diff > 0))
                truep.append(norm.cdf((strength[i] - strength[j] + 3.0) / 12))
        elo.new_season()
    probs, res_, truep = map(np.array, (probs, res_, truep))
    ll = lambda p: -np.mean(res_ * np.log(p) + (1 - res_) * np.log(1 - p))
    print(f"log loss : pile ou face {np.log(2):.4f} | Elo {ll(probs):.4f} | vraies probas {ll(truep):.4f}")


# ----------------------------------------------------------------------------
# BACKTEST SUR DONNÉES RÉELLES (football-data.co.uk) : NON TESTÉ par moi
# ----------------------------------------------------------------------------
def load_football_data(div, years):
    frames = []
    for y in years:
        code = f"{str(y)[2:]}{str(y + 1)[2:]}"
        url = f"https://www.football-data.co.uk/mmz4281/{code}/{div}.csv"
        frames.append(pd.read_csv(url, encoding="latin-1", on_bad_lines="skip"))
    df = pd.concat(frames, ignore_index=True, sort=False)
    df = df.dropna(subset=["HomeTeam", "AwayTeam", "FTHG", "FTAG", "Date"])
    df["date"] = pd.to_datetime(df["Date"], dayfirst=True, format="mixed")
    df = df.rename(columns={"HomeTeam": "home", "AwayTeam": "away", "FTHG": "hg", "FTAG": "ag"})
    return df.sort_values("date").reset_index(drop=True)


def backtest(div, years, xis=(0.0, 0.001, 0.002, 0.004)):
    df = load_football_data(div, years)
    first_test = df[df.date >= f"{years[-1]}-08-01"].date.min()
    print(f"{len(df)} matchs | test = saison {years[-1]}/{years[-1] + 1} à partir du {first_test.date()}")
    train_old = df[df.date < first_test]
    freq = np.bincount(outcome_idx(train_old.hg, train_old.ag), minlength=3) / len(train_old)
    for xi in xis:
        res = walk_forward(df, first_test, xi=xi)
        o = outcome_idx(res.hg.to_numpy(), res.ag.to_numpy())
        P = res[["pH", "pD", "pA"]].to_numpy()
        print(f"xi={xi:<6} n={len(res)} log loss={log_loss(P, o):.4f} RPS={rps(P, o):.4f}")
    PB = np.tile(freq, (len(res), 1))
    print(f"référence fréquences brutes : log loss={log_loss(PB, o):.4f} RPS={rps(PB, o):.4f}")
    if {"PSCH", "PSCD", "PSCA"} <= set(res.columns):
        ok = res[["PSCH", "PSCD", "PSCA"]].notna().all(axis=1)
        PK = np.array([devig_power(r) for r in res.loc[ok, ["PSCH", "PSCD", "PSCA"]].to_numpy()])
        oo = outcome_idx(res.loc[ok, "hg"].to_numpy(), res.loc[ok, "ag"].to_numpy())
        PMo = res.loc[ok, ["pH", "pD", "pA"]].to_numpy()
        print(f"MARCHÉ (Pinnacle clôture, démarginé) : log loss={log_loss(PK, oo):.4f} RPS={rps(PK, oo):.4f}")
        for wgt in (0, .25, .5, .75, 1):
            Pb = wgt * PMo + (1 - wgt) * PK
            print(f"  mélange {wgt:.2f} modèle + {1 - wgt:.2f} marché : log loss={log_loss(Pb, oo):.4f}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--backtest", nargs="+", metavar=("DIV", "ANNEE"))
    a = ap.parse_args()
    if a.selftest:
        selftest()
    elif a.backtest:
        backtest(a.backtest[0], [int(x) for x in a.backtest[1:]])
    else:
        ap.print_help()
