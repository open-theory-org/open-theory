#!/usr/bin/env python3
"""Experiment 6: does the tanh gradient path pass through the teacher-sized MLE?

Same model as tanh_teacher.py (d = 3 inputs, teacher with r tanh units, Gaussian noise).
For each dataset:
  * r-unit MLE: gradient descent on the empirical loss of an r-unit student started at the
    teacher, run to convergence (the regular submodel's maximum-likelihood fit);
  * H-unit student from small initialization (scale eps), plain gradient descent.
Along the H-unit path we record, on 2,000 fresh inputs,
  G(t) = 0.5 E_x (f_t - f0)^2       (generalization error),
  D(t) = 0.5 E_x (f_t - f_MLE)^2    (distance to the r-unit MLE in function space).
Submodel conjecture: min_t D(t) is o(1/n) as eps -> 0, i.e. the path passes through the
r-unit MLE, so n * min_t G(t) -> n * G(MLE_r) -> r (d + 1) / 2 at every width H.

Usage: tanh_submodel.py OUT_JSON [--datasets D] [--seed S] [--r ..] [--H ..] [--n ..]
"""
import argparse
import json
import math

import numpy as np

from tanh_teacher import D, f, potential_grad, teacher


def fit(theta, X, y, H, lr=0.2, steps=40000, tol=1e-9):
    theta = theta[None, :].copy()
    n = len(y)
    for _ in range(steps):
        _, gr = potential_grad(theta, X, y, H)
        gr = (gr - theta) / n
        theta = theta - lr * gr
        if np.abs(gr).max() < tol:
            break
    return theta[0]


def path(X, y, H, rng, Xt, f0t, fm, eps, lr=0.2, steps=60000):
    theta = eps * rng.normal(size=(1, H * (D + 1)))
    n = len(y)
    best_g, best_d, d_at_best_g = math.inf, math.inf, None
    for t in range(steps):
        _, gr = potential_grad(theta, X, y, H)
        theta = theta - lr * (gr - theta) / n
        if t % 20 == 0:
            ft = f(theta[0], Xt, H)
            g = 0.5 * np.mean((ft - f0t) ** 2)
            dd = 0.5 * np.mean((ft - fm) ** 2)
            if g < best_g:
                best_g, d_at_best_g = g, dd
            best_d = min(best_d, dd)
    return best_g, best_d, d_at_best_g


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--datasets", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--r", type=int, nargs="+", default=[1, 2])
    ap.add_argument("--H", type=int, nargs="+", default=None)
    ap.add_argument("--n", type=int, nargs="+", default=[300, 1000, 3000])
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for r in args.r:
        for H in (args.H or [r, 4, 8]):
            for n in args.n:
                for eps in [1e-3, 1e-5]:
                    gm, gb, db, dg = [], [], [], []
                    for _ in range(args.datasets):
                        th0 = teacher(r, rng)
                        X = rng.normal(size=(n, D)); y = f(th0, X, r) + rng.normal(size=n)
                        Xt = rng.normal(size=(2000, D)); f0t = f(th0, Xt, r)
                        thm = fit(th0, X, y, r)
                        fm = f(thm, Xt, r)
                        gm.append(0.5 * np.mean((fm - f0t) ** 2))
                        a, b, c = path(X, y, H, rng, Xt, f0t, fm, eps)
                        gb.append(a); db.append(b); dg.append(c)
                    st = lambda v: dict(mean=float(n * np.mean(v)),
                                        se=float(n * np.std(v, ddof=1) / math.sqrt(len(v))))
                    row = dict(r=r, H=H, n=n, eps=eps, half_dim=r * (D + 1) / 2, mle_r=st(gm),
                               best_on_path=st(gb), min_dist_to_mle=st(db), dist_at_best=st(dg))
                    rows.append(row)
                    print(f"r={r} H={H} n={n:5d} eps={eps:.0e}  n*G(MLE_r)={row['mle_r']['mean']:5.2f}  "
                          f"n*minG={row['best_on_path']['mean']:5.2f}  n*minD={row['min_dist_to_mle']['mean']:7.4f}"
                          f"  n*D@bestG={row['dist_at_best']['mean']:6.3f}", flush=True)
                    with open(args.out, "w") as fh:
                        json.dump(rows, fh, indent=1)


if __name__ == "__main__":
    main()
