#!/usr/bin/env python3
"""Experiment 4b: gradient descent run to an actual stationary point (tanh network).

Experiment 4 stopped gradient descent after a fixed budget, before convergence for
widths H > 1. Here gradient descent (same small init, step and budget as
tanh_teacher.py) is followed by L-BFGS on the same training loss until the
gradient's largest entry is below 1e-8. The result is a stationary point of the
training loss reached from the gradient-descent trajectory, i.e. what "run to
convergence" means. Fresh datasets; same data model as tanh_teacher.py.

Usage: tanh_gdconv.py OUT_JSON --r 1 --H 2 --n 300 [--datasets D]
"""
import argparse
import json
import math

import numpy as np
from scipy.optimize import minimize

from tanh_teacher import D, f, gd, potential_grad, teacher


def loss_and_grad(theta, X, y, H):
    U, g = potential_grad(theta[None, :], X, y, H)
    # remove the prior term: plain mean squared training loss
    n = len(y)
    return (U[0] - 0.5 * (theta ** 2).sum()) / n, (g[0] - theta) / n


def newton_polish(theta, X, y, H, iters=300, tol=1e-9):
    """Levenberg-Marquardt-damped Newton on the training loss, with a finite-difference
    Hessian of the exact gradient; only loss-decreasing steps are accepted."""
    L, g = loss_and_grad(theta, X, y, H)
    mu = 1e-3
    for _ in range(iters):
        if np.abs(g).max() < tol:
            break
        P, h = len(theta), 1e-6
        Hs = np.empty((P, P))
        for i in range(P):
            e = np.zeros(P); e[i] = h
            Hs[:, i] = (loss_and_grad(theta + e, X, y, H)[1] - loss_and_grad(theta - e, X, y, H)[1]) / (2 * h)
        Hs = 0.5 * (Hs + Hs.T)
        lam_min = np.linalg.eigvalsh(Hs).min()
        while True:
            step = -np.linalg.solve(Hs + (max(0.0, -lam_min) + mu) * np.eye(P), g)
            L2, g2 = loss_and_grad(theta + step, X, y, H)
            if L2 <= L:
                theta, L, g, mu = theta + step, L2, g2, max(mu / 3, 1e-12)
                break
            mu *= 4
            if mu > 1e8:
                return theta
    return theta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--r", type=int, default=1)
    ap.add_argument("--H", type=int, default=2)
    ap.add_argument("--n", type=int, default=300)
    ap.add_argument("--datasets", type=int, default=50)
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    gs, grads = [], []
    for _ in range(a.datasets):
        th0 = teacher(a.r, rng)
        X = rng.normal(size=(a.n, D)); y = f(th0, X, a.r) + rng.normal(size=a.n)
        Xt = rng.normal(size=(2000, D)); f0t = f(th0, Xt, a.r)
        th, _, _, _ = gd(X, y, a.H, rng)
        res = minimize(loss_and_grad, th, args=(X, y, a.H), jac=True, method="L-BFGS-B",
                       options=dict(maxiter=200000, gtol=1e-12, ftol=0, maxcor=50))
        th = newton_polish(res.x, X, y, a.H)
        res.x = th
        gr = float(np.abs(loss_and_grad(res.x, X, y, a.H)[1]).max())
        grads.append(gr)
        gs.append(a.n * 0.5 * np.mean((f(res.x, Xt, a.H) - f0t) ** 2))
    gs = np.array(gs)
    row = dict(r=a.r, H=a.H, n=a.n, gd_stationary=dict(mean=float(gs.mean()), se=float(gs.std(ddof=1) / math.sqrt(len(gs)))),
               converged_frac=float(np.mean(np.array(grads) < 1e-6)), max_final_grad=float(max(grads)))
    print(row, flush=True)
    json.dump(row, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
