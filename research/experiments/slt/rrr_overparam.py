#!/usr/bin/env python3
"""Experiment 3: two-layer linear networks with more parameters than examples.

y = B A x + eps, x ~ N(0, I_M), eps ~ N(0, I_N), M = N = 10; teacher of rank r = 2
with singular values `--snr` (default 3). Student widths H; sample sizes n down to
below M (where least squares interpolates) and well below the parameter count
H (M + N). The asymptotic theory (lambda / n) does not apply; we compare
estimators directly by G = ||W - W0||_F^2 / 2.

Estimators: Bayes (Gibbs, as in rrr.py; G from the posterior mean, leading order),
gradient descent from small init (scale 1e-3) run to convergence, stopped by an
80/20 validation split, and the best point on its trajectory (oracle: the
smallest G the trajectory reaches; a lower bound for any stopping rule).

Usage: rrr_overparam.py OUT_JSON --H 2 3 5 10 --n 20 50 ... [--datasets D]
"""
import argparse
import json
import math
import time

import numpy as np

from rrr import gibbs


def truth(M, N, r, snr, rng):
    U, _ = np.linalg.qr(rng.normal(size=(N, N)))
    V, _ = np.linalg.qr(rng.normal(size=(M, M)))
    return (U[:, :r] * snr) @ V[:, :r].T


def data(W0, n, rng):
    X = rng.normal(size=(n, W0.shape[1]))
    return X, X @ W0.T + rng.normal(size=(n, W0.shape[0]))


def gd_path(X, Y, Xv, Yv, H, W0, rng, init=1e-3, steps=200000, tol=1e-9):
    n, M = X.shape
    N = Y.shape[1]
    Sxx, Syx = X.T @ X / n, Y.T @ X / n
    # step small enough for the curvature ||W|| * lambda_max(Sxx) at the solution
    lmax = max(np.linalg.eigvalsh(Sxx).max(), 1.0)
    lr = 0.25 / (lmax * (1.0 + np.linalg.norm(Syx, 2)))
    A = init * rng.normal(size=(H, M))
    B = init * rng.normal(size=(N, H))
    best_val, W_val, best_g = math.inf, None, math.inf
    for t in range(steps):
        W = B @ A
        R = W @ Sxx - Syx
        gA, gB = B.T @ R, R @ A.T
        A, B = A - lr * gA, B - lr * gB
        if t % 10 == 0 and max(np.abs(gA).max(), np.abs(gB).max()) < tol:
            break
        if t % 10 == 0:
            best_g = min(best_g, 0.5 * ((W - W0) ** 2).sum())
            if Xv is not None:
                v = ((Xv @ W.T - Yv) ** 2).mean()
                if v < best_val:
                    best_val, W_val = v, W.copy()
    W = B @ A
    grad = max(np.abs(B.T @ (W @ Sxx - Syx)).max(), np.abs((W @ Sxx - Syx) @ A.T).max())
    return W, W_val, best_g, grad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--M", type=int, default=10)
    ap.add_argument("--r", type=int, default=2)
    ap.add_argument("--snr", type=float, default=3.0)
    ap.add_argument("--H", type=int, nargs="+", default=[2, 3, 5, 10])
    ap.add_argument("--n", type=int, nargs="+", default=[20, 50, 100, 200, 500, 2000])
    ap.add_argument("--datasets", type=int, default=100)
    ap.add_argument("--sweeps", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    M = N = args.M
    out = dict(vars(args), results=[])
    for H in args.H:
        for n in args.n:
            t0 = time.time()
            g = dict(bayes=[], gd_conv=[], gd_early_fair=[], gd_best_on_path=[])
            grads = []
            for _ in range(args.datasets):
                W0 = truth(M, N, args.r, args.snr, rng)
                X, Y = data(W0, n, rng)
                err = lambda W: 0.5 * ((W - W0) ** 2).sum()
                g["bayes"].append(err(gibbs(X.T @ X, Y.T @ X, H, rng, args.sweeps, args.sweeps // 6)))
                Wc, _, gb, gr = gd_path(X, Y, None, None, H, W0, rng)
                grads.append(gr)
                g["gd_conv"].append(err(Wc))
                g["gd_best_on_path"].append(gb)
                k = max((4 * n) // 5, 2)
                _, Wf, _, _ = gd_path(X[:k], Y[:k], X[k:], Y[k:], H, W0, rng)
                g["gd_early_fair"].append(err(Wf))
            row = dict(M=M, N=N, H=H, r=args.r, n=n, params=H * (M + N),
                       gd_final_grad_max=float(np.max(grads)),
                       gd_converged_frac=float(np.mean(np.array(grads) < 1e-6)))
            for key, v in g.items():
                v = np.array(v)
                row[key] = dict(mean=float(v.mean()), se=float(v.std(ddof=1) / math.sqrt(len(v))))
            out["results"].append(row)
            print(f"H={H:2d} n={n:5d} params={row['params']:4d}  " + "  ".join(
                f"{k}={row[k]['mean']:8.3f}±{row[k]['se']:.3f}" for k in g) +
                f"  conv={row['gd_converged_frac']:.2f}" +
                f"  ({time.time() - t0:.0f}s)", flush=True)
            json.dump(out, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
