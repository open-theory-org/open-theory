#!/usr/bin/env python3
"""Robustness checks for experiment 2 (reduced-rank regression).

1. Gibbs convergence. For fixed datasets, compare W-bar from independent chains
   and from 1x vs 4x sweeps. Reports the between-chain spread of n*G relative
   to its value, and the change of n*E[G] when the chains are 4x longer.
2. Plateau sharpening. For gradient descent from random init of scale eps,
   the closest approach of the trajectory to the best rank-r fit W_r, as a
   fraction of ||W_r - W0||. The plateau claim predicts it -> 0 as eps -> 0.

Usage: robustness.py OUT_JSON [--datasets D]
"""
import argparse
import json
import math

import numpy as np

from rrr import data, gibbs, mle, truth

M = N = 4


def gibbs_check(rng, datasets, n=10000):
    out = []
    for r, H in ((1, 4), (1, 6), (2, 4)):
        short, long_, spread = [], [], []
        for _ in range(datasets):
            W0 = truth(M, N, r, rng)
            X, Y = data(W0, n, rng)
            Sxx, Syx = X.T @ X, Y.T @ X
            err = lambda W: n * 0.5 * ((W - W0) ** 2).sum()
            chains = [gibbs(Sxx, Syx, H, rng, 3000, 500, chains=1) for _ in range(4)]
            g = [err(W) for W in chains]
            short.append(err(np.mean(chains, axis=0)))
            spread.append(np.std(g) / max(np.mean(g), 1e-12))
            long_.append(err(gibbs(Sxx, Syx, H, rng, 12000, 2000, chains=4)))
        out.append(dict(r=r, H=H, n=n, nG_3000=float(np.mean(short)), nG_12000=float(np.mean(long_)),
                        se=float(np.std(short, ddof=1) / math.sqrt(datasets)),
                        between_chain_rel_spread=float(np.median(spread))))
        print(out[-1], flush=True)
    return out


def gd_path(X, Y, H, rng, init, Wr, steps):
    n = X.shape[0]
    Sxx, Syx = X.T @ X / n, Y.T @ X / n
    lr = 0.5 / max(np.linalg.eigvalsh(Sxx).max(), 1.0)
    A = init * rng.normal(size=(H, X.shape[1]))
    B = init * rng.normal(size=(Y.shape[1], H))
    best = math.inf
    for _ in range(steps):
        W = B @ A
        best = min(best, ((W - Wr) ** 2).sum())
        R = W @ Sxx - Syx
        A, B = A - lr * B.T @ R, B - lr * R @ A.T
    return math.sqrt(best)


def plateau_check(rng, datasets, n=10000):
    out = []
    for r, H in ((1, 4), (2, 6)):
        for eps in (1e-1, 1e-2, 1e-3, 1e-4, 1e-6):
            rel = []
            for _ in range(datasets):
                W0 = truth(M, N, r, rng)
                X, Y = data(W0, n, rng)
                Wr = mle(X.T @ X, Y.T @ X, r)
                d = gd_path(X, Y, H, rng, eps, Wr, steps=int(4000 * (1 + math.log10(1 / eps))))
                rel.append(d / math.sqrt(((Wr - W0) ** 2).sum()))
            out.append(dict(r=r, H=H, eps=eps, median_rel_dist=float(np.median(rel)),
                            max_rel_dist=float(np.max(rel))))
            print(out[-1], flush=True)
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--datasets", type=int, default=20)
    args = ap.parse_args()
    rng = np.random.default_rng(7)
    res = dict(plateau=plateau_check(rng, args.datasets), gibbs=gibbs_check(rng, args.datasets))
    json.dump(res, open(args.out, "w"), indent=1)
