#!/usr/bin/env python3
"""Experiment 5: the loss-threshold stopping rule (Lean: OpenTheory.Plateau.stopping_rule).

Whitened two-layer linear network: data matrix C = W0 + Z / sqrt(n), Z i.i.d. N(0, 1),
W0 of rank r with singular values 1 (so s2 = 1). Gradient descent on 0.5 ||B A - C||_F^2
(step size lr, time t = steps * lr) from scale eps, either
  * aligned:  A(0) = eps * E V^T, B(0) = eps * U E  (the case covered by the Lean theorem), or
  * random:   A(0), B(0) with i.i.d. N(0, eps^2) entries (not covered).
Rule: t_hat = first time the training loss <= rho; stop at 1.5 * t_hat.
Reported: n * E[G] with G = 0.5 ||W - W0||_F^2, for the stopped network, the truncated SVD
trunc_{s2/2}(C), and the best point on the path (oracle). Theory: r (M + N - r) / 2.

Usage: stopping_rule.py OUT_JSON [--datasets D] [--seed S]
"""
import argparse
import json
import math

import numpy as np


def truth(M, N, r, rng):
    U, _ = np.linalg.qr(rng.normal(size=(N, N)))
    V, _ = np.linalg.qr(rng.normal(size=(M, M)))
    return U[:, :r] @ V[:, :r].T


def trunc(C, tau):
    U, s, Vt = np.linalg.svd(C, full_matrices=False)
    keep = s ** 2 >= tau
    return (U[:, keep] * s[keep]) @ Vt[keep]


def run(C, W0, H, eps, init, rho, rng, lr=0.02, tmax=60.0):
    N, M = C.shape
    if init == "aligned":
        U, s, Vt = np.linalg.svd(C)
        A = eps * np.eye(H, M) @ Vt
        B = eps * U @ np.eye(N, H)
    else:
        A = eps * rng.normal(size=(H, M))
        B = eps * rng.normal(size=(N, H))
    steps = int(tmax / lr)
    hit, stop_step, best, Ws = None, None, math.inf, None
    for k in range(steps + 1):
        W = B @ A
        R = W - C
        if hit is None and 0.5 * (R ** 2).sum() <= rho:
            hit = k
            stop_step = int(math.ceil(1.5 * k))
        g = 0.5 * ((W - W0) ** 2).sum()
        best = min(best, g)
        if stop_step is not None and k == stop_step:
            Ws = W
            break
        A, B = A - lr * B.T @ R, B - lr * R @ A.T
    if Ws is None:
        Ws = B @ A
    return 0.5 * ((Ws - W0) ** 2).sum(), best, (hit or steps) * lr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--datasets", type=int, default=200)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for (M, N, r, H) in [(4, 4, 1, 4), (4, 4, 2, 4), (10, 10, 2, 10)]:
        for n in [100, 1000, 10000]:
            for init in ["aligned", "random"]:
                for rho in [0.25, 0.05]:
                    eps = 1e-5
                    g_stop, g_best, g_svd, t_hats = [], [], [], []
                    for _ in range(args.datasets):
                        W0 = truth(M, N, r, rng)
                        C = W0 + rng.normal(size=(N, M)) / math.sqrt(n)
                        gs, gb, th = run(C, W0, H, eps, init, rho, rng)
                        g_stop.append(gs); g_best.append(gb); t_hats.append(th)
                        g_svd.append(0.5 * ((trunc(C, 0.5) - W0) ** 2).sum())
                    def st(v):
                        v = n * np.array(v)
                        return dict(mean=float(v.mean()), se=float(v.std(ddof=1) / math.sqrt(len(v))))
                    row = dict(M=M, N=N, r=r, H=H, n=n, init=init, rho=rho, eps=eps,
                               theory=r * (M + N - r) / 2, rule=st(g_stop), trunc_svd=st(g_svd),
                               oracle=st(g_best), t_hat=float(np.mean(t_hats)))
                    rows.append(row)
                    print(f"{M}x{N} r={r} H={H} n={n:5d} {init:7s} rho={rho:.2f}  theory={row['theory']:5.1f}  "
                          f"rule={row['rule']['mean']:6.2f}±{row['rule']['se']:.2f}  "
                          f"truncSVD={row['trunc_svd']['mean']:6.2f}  oracle={row['oracle']['mean']:6.2f}  "
                          f"t_hat={row['t_hat']:.1f}", flush=True)
                    with open(args.out, "w") as f:
                        json.dump(rows, f, indent=1)


if __name__ == "__main__":
    main()
