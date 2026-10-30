#!/usr/bin/env python3
"""Experiment 1: Bayes vs maximum-likelihood generalization in singular toy models.

Model:  y = a * b^k * x + eps,   x, eps ~ N(0, 1),   (a, b) ~ Uniform[-1, 1]^2,
        true parameter: a * b^k = 0 (a singular point for every k >= 1).
Also the regular baseline y = w x with w ~ Uniform[-1, 1].

Everything depends on (a, b) only through w = a b^k, and integrating out a gives
the exact prior of w:  P(|W| <= t) =
    regular: t
    k = 1:   t (1 - ln t)
    k = 2:   2 sqrt(t) - t
    k = 3:   (3 t^(1/3) - t) / 2
so the Bayes posterior is one-dimensional and is computed on a fine log-spaced
grid with exact prior cell masses. Data enter only through Sxx = sum x_i^2 and
Sxy = sum x_i y_i, sampled exactly: Sxx ~ chi2(n), Sxy | Sxx ~ N(0, Sxx).

Generalization error (Watanabe):  G_n = E_x KL( q(y|x) || p(y|x, D_n) ).
  * Bayes predictive:  G_n = -E_{x,y ~ N(0,1)} log sum_j pi_j exp(w_j x y - w_j^2 x^2 / 2),
    by Gauss-Hermite quadrature in x and y.
  * Maximum likelihood (= gradient descent run to convergence, since every w in
    [-1, 1] is reachable):  G_n = w_hat^2 / 2,  w_hat = Sxy / Sxx clipped to [-1, 1].
Prediction of singular learning theory:  n E[G_n] -> lambda, the learning
coefficient (real log canonical threshold): 1/2 regular, 1/(2k) for k >= 1.
For k = 1 the multiplicity is 2, so convergence carries a 1/log n correction.

Usage: toy_singular_1d.py OUT_JSON [--datasets N] [--seed S]
"""
import argparse
import json
import math
import os
import time
from multiprocessing import Pool

import numpy as np

MODELS = {
    "regular": dict(lam=0.5, cdf=lambda t: t),
    "k1": dict(lam=0.5, cdf=lambda t: t * (1 - np.log(np.where(t > 0, t, 1.0)))),
    "k2": dict(lam=0.25, cdf=lambda t: 2 * np.sqrt(t) - t),
    "k3": dict(lam=1 / 6, cdf=lambda t: (3 * np.cbrt(t) - t) / 2),
}
NS = [100, 300, 1000, 3000, 10000, 30000]


def grid(cdf, cells=6000):
    """Signed cells on [-1, 1]: log-spaced in |w| from 1e-14, plus the cell at 0."""
    edges = np.concatenate([[0.0], np.logspace(-14, 0, cells)])
    mass = np.diff(cdf(edges)) / 2.0                 # each sign
    mid = np.concatenate([[0.0], np.sqrt(edges[1:-1] * edges[2:])])
    w = np.concatenate([-mid[::-1], mid])
    m = np.concatenate([mass[::-1], mass])
    keep = m > 0
    return w[keep], np.log(m[keep])


GH_X, GH_WX = np.polynomial.hermite_e.hermegauss(48)
GH_WX = GH_WX / GH_WX.sum()


def bayes_G(w, logm, sxx, sxy):
    logpost = logm + w * sxy - 0.5 * w * w * sxx
    logpost -= logpost.max()
    keep = logpost > -60
    w, lp = w[keep], logpost[keep]
    lp = lp - np.log(np.exp(lp).sum())
    x = GH_X[:, None, None]
    y = GH_X[None, :, None]
    expo = lp[None, None, :] + w[None, None, :] * x * y - 0.5 * (w[None, None, :] * x) ** 2
    mx = expo.max(axis=2, keepdims=True)
    lse = (mx + np.log(np.exp(expo - mx).sum(axis=2, keepdims=True)))[:, :, 0]
    wbar = float((np.exp(lp) * w).sum())
    return float(-(GH_WX[:, None] * GH_WX[None, :] * lse).sum()), wbar


def _chunk(args):
    sxx, sxy = args
    grids = {name: grid(spec["cdf"]) for name, spec in MODELS.items()}
    return {name: [bayes_G(w, logm, a, b) for a, b in zip(sxx, sxy)] for name, (w, logm) in grids.items()}


def summary(g, n):
    return dict(mean=float(g.mean()), se=float(g.std(ddof=1) / math.sqrt(len(g))))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--datasets", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    with Pool(args.workers) as pool:
        run(args, rng, pool)


def run(args, rng, pool):
    out = dict(datasets=args.datasets, seed=args.seed, ns=NS, results={})
    for n in NS:
        t0 = time.time()
        sxx = rng.chisquare(n, args.datasets)
        sxy = rng.normal(0.0, np.sqrt(sxx))
        what = np.clip(sxy / sxx, -1, 1)
        g_mle = what ** 2 / 2
        row = dict(mle=dict(mean=float(g_mle.mean()), se=float(g_mle.std(ddof=1) / math.sqrt(len(g_mle)))))
        parts = pool.map(_chunk, [(a, b) for a, b in zip(np.array_split(sxx, min(4 * args.workers, len(sxx))),
                                                         np.array_split(sxy, min(4 * args.workers, len(sxy))))])
        for name in MODELS:
            res = np.concatenate([np.asarray(part[name], dtype=float).reshape(-1, 2) for part in parts])
            row[name] = summary(res[:, 0], n)
            # leading-order identity used in rrr.py: G = wbar^2 / 2 + O(n^-2)
            row[name + "_wbar_sq_half"] = summary(res[:, 1] ** 2 / 2, n)
        out["results"][n] = row
        msg = "  ".join(f"{k}: {n * v['mean']:.4f}±{n * v['se']:.4f}" for k, v in row.items())
        print(f"n={n:6d}  n*E[G]  {msg}   ({time.time() - t0:.0f}s)", flush=True)
    out["lambda"] = {name: spec["lam"] for name, spec in MODELS.items()}
    with open(args.out, "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
