#!/usr/bin/env python3
"""Experiment 4: a nonlinear (tanh) two-layer network, teacher-student.

f(x) = sum_j c_j tanh(w_j . x), x ~ N(0, I_d), y = f0(x) + N(0, 1), d = 3.
Teacher: r units with unit-norm directions scaled by 1.5 and c_j = 1. Student:
H >= r units, prior N(0, 1) on every weight.

G = (1/2) E_x (f(x) - f0(x))^2 (the KL for Gaussian noise); for the Bayes
predictive, G = (1/2) E_x (posterior-mean f - f0)^2 to leading order (as in
rrr.py). E_x is estimated on 2,000 fresh test inputs.

Estimators:
  * Bayes: Hamiltonian Monte Carlo, 4 chains, step size adapted in warmup.
    Sanity check: for H = r the model is regular and n E[G] -> r (d + 1) / 2.
  * Gradient descent from small init (scale 1e-3): run to convergence, stopped
    by an 80/20 validation split, and the best point on its trajectory (oracle).
λ is not known in closed form here; the question is how each estimator depends
on the width H.

Usage: tanh_teacher.py OUT_JSON --r 1 --H 1 2 4 8 --n 300 1000 3000 [--datasets D]
"""
import argparse
import json
import math
import time

import numpy as np

D = 3


def f(theta, X, H):
    W = theta[..., :H * D].reshape(theta.shape[:-1] + (H, D))
    c = theta[..., H * D:]
    return np.einsum("...h,...nh->...n", c, np.tanh(np.einsum("...hd,nd->...nh", W, X)))


def potential_grad(theta, X, y, H):
    """U = 0.5 ||y - f||^2 + 0.5 ||theta||^2 and its gradient (theta: chains x P)."""
    W = theta[:, :H * D].reshape(-1, H, D)
    c = theta[:, H * D:]
    T = np.tanh(np.einsum("khd,nd->knh", W, X))          # chains x n x H
    r = y[None, :] - np.einsum("kh,knh->kn", c, T)
    U = 0.5 * (r ** 2).sum(1) + 0.5 * (theta ** 2).sum(1)
    gc = -np.einsum("kn,knh->kh", r, T) + c
    gW = -np.einsum("kn,kh,knh,nd->khd", r, c, 1 - T ** 2, X) + W
    return U, np.concatenate([gW.reshape(len(theta), -1), gc], axis=1)


def hmc(X, y, H, rng, chains=4, warmup=1500, samples=1500, L=30):
    P = H * (D + 1)
    theta = 0.5 * rng.normal(size=(chains, P))
    eps = np.full(chains, 0.01)
    U, g = potential_grad(theta, X, y, H)
    draws, acc_hist = [], []
    for it in range(warmup + samples):
        e = eps * np.exp(0.2 * rng.uniform(-1, 1, size=chains))     # jitter
        p0 = rng.normal(size=theta.shape)
        q, p, gq = theta.copy(), p0 - 0.5 * e[:, None] * g, g
        for l in range(L):
            q = q + e[:, None] * p
            Uq, gq = potential_grad(q, X, y, H)
            if l < L - 1:
                p = p - e[:, None] * gq
        p = p - 0.5 * e[:, None] * gq
        logacc = (U + 0.5 * (p0 ** 2).sum(1)) - (Uq + 0.5 * (p ** 2).sum(1))
        accept = np.log(rng.uniform(size=chains)) < np.nan_to_num(logacc, nan=-np.inf)
        theta[accept], U[accept], g[accept] = q[accept], Uq[accept], gq[accept]
        a = np.minimum(1.0, np.exp(np.minimum(np.nan_to_num(logacc, nan=-50.0), 0.0)))
        if it < warmup:
            eps *= np.exp(0.05 * (a - 0.75))
        else:
            draws.append(theta.copy())
            acc_hist.append(a.mean())
    return np.array(draws), float(np.mean(acc_hist))   # samples x chains x P


def gd(X, y, H, rng, Xv=None, yv=None, Xt=None, f0t=None, init=1e-3, steps=60000, tol=1e-8):
    P = H * (D + 1)
    theta = init * rng.normal(size=(1, P))
    n = len(y)
    lr = 0.2
    best_val, th_val, best_g = math.inf, None, math.inf
    for t in range(steps):
        _, gr = potential_grad(theta, X, y, H)
        gr = (gr - theta) / n                    # gradient of the mean squared loss only
        theta = theta - lr * gr
        if t % 20 == 0:
            if Xt is not None:
                best_g = min(best_g, 0.5 * np.mean((f(theta[0], Xt, H) - f0t) ** 2))
            if Xv is not None:
                v = np.mean((f(theta[0], Xv, H) - yv) ** 2)
                if v < best_val:
                    best_val, th_val = v, theta[0].copy()
            if np.abs(gr).max() < tol:
                break
    _, gr = potential_grad(theta, X, y, H)
    return theta[0], th_val, best_g, float(np.abs((gr - theta) / n).max())


def teacher(r, rng):
    Wt = rng.normal(size=(r, D))
    Wt = 1.5 * Wt / np.linalg.norm(Wt, axis=1, keepdims=True)
    return np.concatenate([Wt.ravel(), np.ones(r)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--r", type=int, default=1)
    ap.add_argument("--H", type=int, nargs="+", default=[1, 2, 4, 8])
    ap.add_argument("--n", type=int, nargs="+", default=[300, 1000, 3000])
    ap.add_argument("--datasets", type=int, default=50)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    out = dict(vars(args), results=[])
    for H in args.H:
        for n in args.n:
            t0 = time.time()
            g = dict(bayes=[], gd_conv=[], gd_early_fair=[], gd_best_on_path=[])
            accs, grads = [], []
            for _ in range(args.datasets):
                th0 = teacher(args.r, rng)
                X = rng.normal(size=(n, D)); y = f(th0, X, args.r) + rng.normal(size=n)
                Xt = rng.normal(size=(2000, D)); f0t = f(th0, Xt, args.r)
                draws, acc = hmc(X, y, H, rng)
                fbar = f(draws.reshape(-1, draws.shape[-1]), Xt, H).mean(0)
                g["bayes"].append(0.5 * np.mean((fbar - f0t) ** 2)); accs.append(acc)
                thc, _, gb, gr = gd(X, y, H, rng, Xt=Xt, f0t=f0t)
                g["gd_conv"].append(0.5 * np.mean((f(thc, Xt, H) - f0t) ** 2))
                g["gd_best_on_path"].append(gb); grads.append(gr)
                k = (4 * n) // 5
                _, thv, _, _ = gd(X[:k], y[:k], H, rng, Xv=X[k:], yv=y[k:])
                g["gd_early_fair"].append(0.5 * np.mean((f(thv, Xt, H) - f0t) ** 2))
            row = dict(d=D, r=args.r, H=H, n=n, params=H * (D + 1), regular_half_dim=args.r * (D + 1) / 2,
                       hmc_accept=float(np.mean(accs)), gd_converged_frac=float(np.mean(np.array(grads) < 1e-6)))
            for key, v in g.items():
                v = n * np.array(v)
                row[key] = dict(mean=float(v.mean()), se=float(v.std(ddof=1) / math.sqrt(len(v))))
            out["results"].append(row)
            print(f"r={args.r} H={H} n={n:5d}  n*E[G]: " + "  ".join(
                f"{k}={row[k]['mean']:6.2f}±{row[k]['se']:.2f}" for k in g) +
                f"  acc={row['hmc_accept']:.2f} conv={row['gd_converged_frac']:.2f} ({time.time() - t0:.0f}s)",
                flush=True)
            json.dump(out, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
