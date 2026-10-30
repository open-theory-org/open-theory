#!/usr/bin/env python3
"""Experiment 2: reduced-rank regression (a two-layer linear network).

Model:   y = B A x + eps,  x ~ N(0, I_M),  eps ~ N(0, I_N),  A: H×M,  B: N×H,
         prior: all entries of A and B i.i.d. N(0, 1).
Truth:   W0 = B0 A0 of rank r (singular values fixed, random singular vectors).

Generalization error of a predictor y ~ N(W x, I): G = E_x KL(q || p) = ||W - W0||_F^2 / 2.
For the Bayes predictive (a posterior mixture) G = ||E[W | D] - W0||_F^2 / 2 + O(n^-2),
by a cumulant expansion of the log-mixture (validated in toy_singular_1d.py).

Estimators compared, as n E[G_n]:
  * Bayes: Gibbs sampling, alternating the exact Gaussian conditionals of B | A and
    A | B. W-bar is Rao-Blackwellized as E[ E[B | A] A ].
  * MLE: rank-min(H, M, N) least squares (Eckart–Young on the OLS fit under Sxx).
  * GD: full-batch gradient descent on the empirical loss from small random init,
    (i) run to convergence, (ii) stopped at the iterate with the lowest loss on a
    held-out set of n/4 extra draws (what practice does).
Theory: n E[G_Bayes] -> lambda(M, N, H, r) (Aoyagi & Watanabe 2005).

Usage: rrr.py OUT_JSON --M 4 --N 4 --H 1 2 3 4 6 --r 0 1 2 --n 1000 ... [--datasets D]
"""
import argparse
import json
import math
import time

import numpy as np


def rlct(M, N, H, r):
    """Learning coefficient of reduced-rank regression (Aoyagi & Watanabe 2005)."""
    if N + r <= M + H and M + r <= N + H and H + r <= M + N:
        s = 2 * (H + r) * (M + N) - (M - N) ** 2 - (H + r) ** 2
        return (s + ((M + H + N + r) % 2)) / 8
    if M + H < N + r:
        return (H * M - H * r + N * r) / 2
    if N + H < M + r:
        return (H * N - H * r + M * r) / 2
    return M * N / 2   # M + N < H + r


def truth(M, N, r, rng):
    U, _ = np.linalg.qr(rng.normal(size=(N, N)))
    V, _ = np.linalg.qr(rng.normal(size=(M, M)))
    return (U[:, :r] * 1.0) @ V[:, :r].T   # singular values 1


def data(W0, n, rng):
    M = W0.shape[1]
    X = rng.normal(size=(n, M))
    Y = X @ W0.T + rng.normal(size=(n, W0.shape[0]))
    return X, Y


def mle(Sxx, Syx, H):
    """argmin_{rank W <= H} sum ||y - W x||^2 = Eckart–Young in the Sxx metric."""
    Wols = np.linalg.solve(Sxx, Syx.T).T
    L = np.linalg.cholesky(Sxx)                      # Sxx = L L^T
    U, s, Vt = np.linalg.svd(Wols @ L, full_matrices=False)
    k = min(H, len(s))
    return (U[:, :k] * s[:k]) @ Vt[:k] @ np.linalg.inv(L)


def gibbs(Sxx, Syx, H, rng, sweeps, burn, chains=4):
    N, M = Syx.shape
    Wbar = np.zeros((N, M))
    for _ in range(chains):
        A = rng.normal(size=(H, M))
        acc, cnt = np.zeros((N, M)), 0
        for t in range(sweeps):
            # B | A: rows i.i.d. Gaussian with precision P = A Sxx A^T + I
            P = A @ Sxx @ A.T + np.eye(H)
            C = np.linalg.cholesky(P)
            mean = np.linalg.solve(P, A @ Syx.T).T    # N×H
            B = mean + np.linalg.solve(C.T, rng.normal(size=(H, N))).T
            # A | B: vec(A) Gaussian with precision kron(Sxx, B^T B) + I
            Q = np.kron(Sxx, B.T @ B) + np.eye(H * M)
            CQ = np.linalg.cholesky(Q)
            rhs = (B.T @ Syx).reshape(-1, order="F")
            mu = np.linalg.solve(Q, rhs)
            A = (mu + np.linalg.solve(CQ.T, rng.normal(size=H * M))).reshape(H, M, order="F")
            if t >= burn:
                # Rao-Blackwellized W-bar given A: E[B | A] A
                P = A @ Sxx @ A.T + np.eye(H)
                acc += np.linalg.solve(P, A @ Syx.T).T @ A
                cnt += 1
        Wbar += acc / cnt
    return Wbar / chains


def gd(X, Y, Xv, Yv, H, rng, init=1e-3, steps=20000, tol=1e-12, ref=None):
    n, M = X.shape
    N = Y.shape[1]
    Sxx, Syx = X.T @ X / n, Y.T @ X / n
    lr = 0.5 / max(np.linalg.eigvalsh(Sxx).max(), 1.0)
    A = init * rng.normal(size=(H, M))
    B = init * rng.normal(size=(N, H))
    best, Wbest = math.inf, None
    closest, Wclose = math.inf, None
    for t in range(steps):
        W = B @ A
        R = W @ Sxx - Syx                  # gradient of (1/2n) sum ||W x - y||^2 w.r.t. W
        gA, gB = B.T @ R, R @ A.T
        A -= lr * gA
        B -= lr * gB
        if t % 20 == 0:
            v = ((Xv @ W.T - Yv) ** 2).mean()
            if v < best:
                best, Wbest = v, W.copy()
            if ref is not None:
                dist = ((W - ref) ** 2).sum()
                if dist < closest:
                    closest, Wclose = dist, W.copy()
            if np.abs(R).max() < tol:
                break
    return B @ A, Wbest, Wclose


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--M", type=int, default=4)
    ap.add_argument("--N", type=int, default=4)
    ap.add_argument("--H", type=int, nargs="+", default=[1, 2, 3, 4, 6])
    ap.add_argument("--r", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--n", type=int, nargs="+", default=[300, 1000, 3000, 10000])
    ap.add_argument("--datasets", type=int, default=100)
    ap.add_argument("--sweeps", type=int, default=3000)
    ap.add_argument("--burn", type=int, default=500)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    M, N = args.M, args.N
    out = dict(vars(args), results=[])
    for r in args.r:
        for H in args.H:
            lam = rlct(M, N, H, r)
            for n in args.n:
                t0 = time.time()
                g = dict(bayes=[], mle=[], gd_conv=[], gd_early=[], gd_early_fair=[], rank_r_mle=[],
                         gd_plateau=[])
                for d in range(args.datasets):
                    W0 = truth(M, N, r, rng)
                    X, Y = data(W0, n, rng)
                    Xv, Yv = data(W0, max(n // 4, 50), rng)
                    Sxx, Syx = X.T @ X, Y.T @ X
                    err = lambda W: 0.5 * ((W - W0) ** 2).sum()
                    g["bayes"].append(err(gibbs(Sxx, Syx, H, rng, args.sweeps, args.burn)))
                    g["mle"].append(err(mle(Sxx, Syx, H)))
                    Wr = mle(Sxx, Syx, max(r, 1)) if r > 0 else np.zeros_like(W0)
                    g["rank_r_mle"].append(err(Wr))
                    Wc, We, Wp = gd(X, Y, Xv, Yv, H, rng, ref=Wr)
                    g["gd_conv"].append(err(Wc))
                    g["gd_early"].append(err(We))
                    # trajectory's closest approach to the rank-r fit (the predicted plateau)
                    g["gd_plateau"].append(err(Wp))
                    # early stopping without extra data: train on 80% of the n, validate on 20%
                    k = (4 * n) // 5
                    _, Wf, _ = gd(X[:k], Y[:k], X[k:], Y[k:], H, rng)
                    g["gd_early_fair"].append(err(Wf))
                row = dict(M=M, N=N, H=H, r=r, n=n, lam=lam, params=H * (M + N))
                for k, v in g.items():
                    v = np.array(v)
                    row[k] = dict(mean=float(n * v.mean()), se=float(n * v.std(ddof=1) / math.sqrt(len(v))))
                out["results"].append(row)
                print(f"r={r} H={H} n={n:6d} lambda={lam:5.2f}  " + "  ".join(
                    f"{k}={row[k]['mean']:6.2f}±{row[k]['se']:.2f}" for k in g) +
                    f"  ({time.time() - t0:.0f}s)", flush=True)
                with open(args.out, "w") as f:
                    json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
