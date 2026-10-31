#!/usr/bin/env python3
"""Untrusted producer of `mlp-exact` certificates (checked by `formal/core/Checks/MLP.lean`).

A certificate claims that a ReLU network with integer weights outputs exactly `Y` on the input
`x`. This module packs the network, the input and the claimed outputs into the short
certificate `s c wb D a0 U Y (n a E lg PW B)*` that `ot_kernel mlp-exact` / `ot_check mlp-exact`
accept. Nothing here is trusted: the check recomputes everything it relies on.

Weights are integers in `[-c, 2**wb - c)`; the defaults (`wb = 2`, `c = 2`) give the
`{-2, ..., 1}` codes of the repository's quantized MLPs.
"""
from __future__ import annotations

import random

WB, C = 2, 2  # weight digits in [0, 4), weight = digit - 2


def pack(digits: list[int], s: int) -> int:
    """Digits in base 2**s, slot 0 first (linear time via one binary string)."""
    assert all(0 <= d < 1 << s for d in digits)
    return int("".join(format(d, f"0{s}b") for d in reversed(digits)) or "0", 2)


def forward(layers, x):
    """Pre-activations of every layer; ReLU between layers, none after the last."""
    acts, u = [], x
    for li, (W, b) in enumerate(layers):
        y = [sum(w * v for w, v in zip(row, u)) + bi for row, bi in zip(W, b)]
        acts.append(y)
        u = y if li == len(layers) - 1 else [max(v, 0) for v in y]
    return acts


def random_network(dims, a0, rng):
    x = [rng.randrange(1 << a0) for _ in range(dims[0])]
    layers, u = [], x
    for l in range(len(dims) - 1):
        W = [[rng.randrange(1 << WB) - C for _ in range(dims[l])] for _ in range(dims[l + 1])]
        # centre each unit on this input, so about half the hidden units are active
        mean = sum(u) // len(u)
        b = [-sum(row) * mean + rng.randrange(-8, 9) for row in W]
        layers.append((W, b))
        u = [max(v, 0) for v in forward([(W, b)], u)[0]]
    return layers, x


def certificate(layers, x, a0, claimed=None):
    """Short certificate `s c wb D a0 U Y (n a E lg PW B)*` claiming outputs `claimed`."""
    dims = [len(x)] + [len(b) for _, b in layers]
    acts = forward(layers, x)
    out = acts[-1] if claimed is None else claimed
    bounds = [a0] + [max(1, max(max(v, 0) for v in y).bit_length()) for y in acts[:-1]]
    s = max((dims[l] * ((1 << WB) - 1) * ((1 << bounds[l]) - 1)).bit_length() + 2
            for l in range(len(layers)))
    off = 1 << (s - 1)
    args = [s, C, WB, dims[0], a0, pack(x, s), pack([v + off for v in out], s)]
    for l, (W, b) in enumerate(layers):
        D, n = dims[l], dims[l + 1]
        E = max(D, n + 1)                 # row spacing: rows fit, and the gather has room
        lg = max(0, (n - 1).bit_length())  # gather rounds: n <= 2**lg
        pw = pack([W[i][D - 1 - r] + C if r < D else 0 for i in range(n) for r in range(E)], s)
        a = bounds[l + 1] if l + 1 < len(layers) else 0
        args += [n, a, E, lg, pw, pack([bi + off for bi in b], s)]
    return args


def request(args) -> str:
    return "mlp-exact " + " ".join(hex(a) for a in args)


def tampered(layers, x, a0, rng):
    """Three false claims: wrong output; honest output with a changed weight; with a changed input."""
    y = forward(layers, x)[-1]
    yield certificate(layers, x, a0, claimed=[y[0] + 1] + y[1:])
    for _ in range(10000):  # a weight whose change reaches the output
        i, k = rng.randrange(len(layers[0][0])), rng.randrange(len(x))
        W, b = layers[0]
        d = W[i][k] + C
        W2 = [row[:] for row in W]
        W2[i][k] += 1 if d + 1 < 1 << WB else -1
        if forward([(W2, b)] + layers[1:], x)[-1] != y:
            yield certificate([(W2, b)] + layers[1:], x, a0, claimed=y)
            break
    for _ in range(10000):  # an input pixel whose change reaches the output
        k = rng.randrange(len(x))
        x2 = x[:]
        x2[k] += 1 if x[k] + 1 < 1 << a0 else -1
        if forward(layers, x2)[-1] != y:
            yield certificate(layers, x2, a0, claimed=y)
            break
