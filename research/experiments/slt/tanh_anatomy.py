#!/usr/bin/env python3
"""Experiment 7: anatomy of the tanh plateau.

Same model as tanh_teacher.py (d = 3, r-unit teacher, Gaussian noise). For each dataset we run
plain gradient descent from small initialization for much longer than experiment 6 (1e6 steps),
and at log-spaced checkpoints record:
  * train loss, G(t) = 0.5 E(f_t - f0)^2, D(t) = 0.5 E(f_t - f_MLE)^2 (distance to the r-unit MLE);
  * per unit: |w_j|, c_j, and |cos| with each teacher direction (tanh is odd: (w, c) ~ (-w, -c));
  * condensation: units are assigned to their nearest teacher direction; within each cluster we
    measure the spread of the sign-aligned weight vectors (0 = exact duplicates, i.e. the student
    sits on the Fukumizu-Amari embedding of an r-unit network);
  * D_merge(t): distance from f_t to the r-unit network obtained by merging each cluster
    (mean weight vector, summed output weight). D_merge = 0 on the duplication line.
Question: does D(t) keep falling with time (slow approach to the embedded r-unit MLE), or does the
path settle at a point that is not on the duplication line?

Usage: tanh_anatomy.py OUT_JSON [--datasets D] [--steps S] [--eps E] [--workers W]
"""
import argparse
import json
import math
from multiprocessing import Pool

import numpy as np

from tanh_teacher import D, f, potential_grad, teacher
from tanh_submodel import fit


def unpack(theta, H):
    return theta[:H * D].reshape(H, D), theta[H * D:]


def merged(theta, H, dirs):
    """Merge units by nearest teacher direction: sign-align, average w, sum c."""
    W, c = unpack(theta, H)
    r = len(dirs)
    cos = (W @ dirs.T) / (np.linalg.norm(W, axis=1, keepdims=True) + 1e-300)
    k = np.argmax(np.abs(cos), axis=1)
    s = np.sign(cos[np.arange(H), k])
    Wm, cm, spread = np.zeros((r, D)), np.zeros(r), np.zeros(r)
    for j in range(r):
        idx = np.where(k == j)[0]
        if len(idx) == 0:
            continue
        Wa = W[idx] * s[idx, None]
        ca = c[idx] * s[idx]
        weight = np.abs(ca) * np.linalg.norm(Wa, axis=1)
        if weight.sum() == 0:
            continue
        wbar = (weight[:, None] * Wa).sum(0) / weight.sum()
        Wm[j], cm[j] = wbar, ca.sum()
        big = weight > 0.01 * weight.sum()
        spread[j] = float(np.max(np.linalg.norm(Wa[big] - wbar, axis=1)) / (np.linalg.norm(wbar) + 1e-300))
    return np.concatenate([Wm.ravel(), cm]), spread, k, s


def run(job):
    r, H, n, eps, steps, seed = job
    rng = np.random.default_rng(seed)
    th0 = teacher(r, rng)
    dirs = unpack(th0, r)[0] / 1.5
    X = rng.normal(size=(n, D)); y = f(th0, X, r) + rng.normal(size=n)
    Xt = rng.normal(size=(4000, D)); f0t = f(th0, Xt, r)
    thm = fit(th0, X, y, r, steps=200000, tol=1e-11)
    fm = f(thm, Xt, r)
    theta = eps * rng.normal(size=(1, H * (D + 1)))
    checkpoints = sorted(set(np.unique(np.logspace(0, math.log10(steps), 160).astype(int)).tolist()))
    lr, out = 0.2, []
    ci = 0
    for t in range(steps + 1):
        if t == checkpoints[ci]:
            th = theta[0]
            ft = f(th, Xt, H)
            W, c = unpack(th, H)
            thmg, spread, k, s = merged(th, H, dirs)
            fmg = f(thmg, Xt, r)
            out.append(dict(
                t=t, train=float(0.5 * np.mean((f(th, X, H) - y) ** 2)),
                G=float(0.5 * np.mean((ft - f0t) ** 2)), Dm=float(0.5 * np.mean((ft - fm) ** 2)),
                Dmerge=float(0.5 * np.mean((ft - fmg) ** 2)),
                norms=np.linalg.norm(W, axis=1).tolist(), c=c.tolist(),
                cos=(np.abs(W @ dirs.T) / (np.linalg.norm(W, axis=1, keepdims=True) + 1e-300)).tolist(),
                spread=spread.tolist(), cluster=k.tolist()))
            ci += 1
            if ci == len(checkpoints):
                break
        _, gr = potential_grad(theta, X, y, H)
        theta = theta - lr * (gr - theta) / n
    G_mle = float(0.5 * np.mean((fm - f0t) ** 2))
    return dict(r=r, H=H, n=n, eps=eps, seed=seed, G_mle=G_mle, theta_mle=thm.tolist(), path=out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--datasets", type=int, default=8)
    ap.add_argument("--steps", type=int, default=1_000_000)
    ap.add_argument("--eps", type=float, default=1e-5)
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--workers", type=int, default=9)
    args = ap.parse_args()
    jobs = [(r, H, args.n, args.eps, args.steps, 1000 * r + 100 * H + i)
            for r in (1, 2) for H in (4, 8) for i in range(args.datasets)]
    with Pool(args.workers) as pool:
        res = pool.map(run, jobs)
    with open(args.out, "w") as fh:
        json.dump(res, fh)


if __name__ == "__main__":
    main()
