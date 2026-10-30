#!/usr/bin/env python3
"""Feasibility study: training-data-only Occam bounds for compressed MNIST nets.

Usage: mnist_occam_feasibility.py MNIST_DIR OUT_JSON [--configs NAME,...]

No held-out data enters the bound. For a countable family with a prefix-free
code of length L(h) bits fixed before seeing the data, with probability at least
1 - δ over n IID training points, every h satisfies
    P(Bin(n, R_h) ≤ K_h) > δ 2^{-L(h)}
(union bound over h with weights 2^{-L(h)}, Kraft). The certified rate is the
Clopper–Pearson upper bound at level δ 2^{-L(h)} ("binomial Occam"). The
kl-inversion form kl(K/n ‖ R) ≤ (L ln 2 + ln(1/δ)) / n is reported for reference.

Hypotheses are integer networks: integer pixels in [0, 255] (optionally summed
over fixed pooling blocks), ternary weights, integer biases, ReLU, argmax with
the first maximum winning. Training errors are counted with an exact int64
forward pass of that integer network, not with the float surrogate.

Code for one network (all parts prefix-free, fixed before training):
  * the configuration index among the declared CONFIGS: log2 |CONFIGS| bits;
  * per weight layer: counts of the symbols -1 and +1, each in ceil(log2(P+1))
    bits, then the weights given the counts by an enumerative code of
    ceil(log2 multinomial(P; n_-1, n_0, n_+1)) bits;
  * each integer bias: signed Elias-delta code.
Training hyperparameters are part of the declared configuration, so the search
over CONFIGS is paid for. The study itself looked at results while designing
the configs; a certificate must fix its configs before training.
"""
import argparse
import gzip
import json
import math
import time
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

DELTA = 0.05


def load_idx(path):
    with gzip.open(path, "rb") as f:
        data = f.read()
    magic = int.from_bytes(data[:4], "big")
    dims = [int.from_bytes(data[4 + 4 * i:8 + 4 * i], "big") for i in range(magic & 0xFF)]
    return np.frombuffer(data, dtype=np.uint8, offset=4 + 4 * len(dims)).reshape(dims)


def load_mnist(d):
    d = Path(d)
    xtr = load_idx(d / "train-images-idx3-ubyte.gz").astype(np.int64)
    ytr = load_idx(d / "train-labels-idx1-ubyte.gz").astype(np.int64)
    xte = load_idx(d / "t10k-images-idx3-ubyte.gz").astype(np.int64)
    yte = load_idx(d / "t10k-labels-idx1-ubyte.gz").astype(np.int64)
    return xtr, ytr, xte, yte


def pool(x, k):
    """Integer sum over k×k blocks (a fixed preprocessing, part of the decoder)."""
    if k == 1:
        return x
    n, h, w = x.shape
    return x.reshape(n, h // k, k, w // k, k).sum(axis=(2, 4))


# ---------------------------------------------------------------- bounds

def log_binom_cdf(n, k, p):
    if p <= 0:
        return 0.0
    if p >= 1:
        return 0.0 if k >= n else -math.inf
    i = np.arange(k + 1)
    t = (np.array([math.lgamma(n + 1) - math.lgamma(j + 1) - math.lgamma(n - j + 1) for j in i])
         + i * math.log(p) + (n - i) * math.log1p(-p))
    m = t.max()
    return float(m + math.log(np.exp(t - m).sum()))


def binomial_occam(n, k, bits, delta=DELTA):
    """Largest p with P(Bin(n,p) ≤ k) ≥ δ 2^{-bits}: the certified error rate."""
    target = math.log(delta) - bits * math.log(2)
    lo, hi = k / n, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if log_binom_cdf(n, k, mid) >= target:
            lo = mid
        else:
            hi = mid
    return hi


def kl_occam(n, k, bits, delta=DELTA):
    q, c = k / n, (bits * math.log(2) + math.log(1 / delta)) / n

    def kl(q, p):
        a = q * math.log(q / p) if q > 0 else 0.0
        return a + (1 - q) * math.log((1 - q) / (1 - p))
    lo, hi = q, 1 - 1e-15
    for _ in range(100):
        mid = (lo + hi) / 2
        if kl(q, mid) <= c:
            lo = mid
        else:
            hi = mid
    return hi


# ---------------------------------------------------------------- code length

def log2_multinomial(counts):
    total = sum(counts)
    return (math.lgamma(total + 1) - sum(math.lgamma(c + 1) for c in counts)) / math.log(2)


def ternary_layer_bits(q):
    q = np.asarray(q).ravel()
    p = q.size
    counts = [int((q == v).sum()) for v in (-1, 0, 1)]
    header = 2 * math.ceil(math.log2(p + 1))
    return header + math.ceil(log2_multinomial(counts)), counts


def elias_delta_bits(m):
    """Length of the Elias-delta code of a positive integer m."""
    nb = m.bit_length()
    return nb - 1 + 2 * (nb.bit_length() - 1) + 1


def signed_int_bits(z):
    return elias_delta_bits(2 * z + 1 if z >= 0 else -2 * z)  # 0,-1,1,-2,... -> 1,2,3,4,...


# ---------------------------------------------------------------- models

class TernarySTE(torch.autograd.Function):
    @staticmethod
    def forward(ctx, w, thr):
        return torch.where(w.abs() > thr, torch.sign(w), torch.zeros_like(w))

    @staticmethod
    def backward(ctx, g):
        return g, None


def ternarize(w, t):
    thr = t * w.abs().mean()
    q = TernarySTE.apply(w, thr)
    nz = (q != 0).float()
    alpha = (w.abs() * nz).sum() / nz.sum().clamp(min=1)
    return q, alpha


class TernaryMLP(nn.Module):
    """x (pixel sums) -> ReLU(α1 Q1 x/255 + b1) -> α2 Q2 h + b2."""

    def __init__(self, d, h, t):
        super().__init__()
        self.w1 = nn.Parameter(torch.randn(h, d) / math.sqrt(d))
        self.b1 = nn.Parameter(torch.zeros(h))
        self.w2 = nn.Parameter(torch.randn(10, h) / math.sqrt(h))
        self.b2 = nn.Parameter(torch.zeros(10))
        self.t = t

    def forward(self, x):
        q1, a1 = ternarize(self.w1, self.t)
        q2, a2 = ternarize(self.w2, self.t)
        hid = F.relu(a1 * (x @ q1.T) + self.b1)
        return a2 * (hid @ q2.T) + self.b2

    def integer_net(self, scale_in):
        """Integer biases at the scale of the integer pre-activations."""
        with torch.no_grad():
            q1, a1 = ternarize(self.w1, self.t)
            q2, a2 = ternarize(self.w2, self.t)
            # float input is x_int / scale_in, so α1 Q1 x + b1 = (α1/scale_in)(Q1 x_int + b1 scale_in/α1)
            s1 = (a1 / scale_in).item()
            B1 = torch.round(self.b1 / s1)
            s2 = s1 * a2.item()
            B2 = torch.round(self.b2 / s2)
        f = lambda t: t.detach().cpu().numpy().astype(np.int64)
        return dict(Q1=f(q1), B1=f(B1), Q2=f(q2), B2=f(B2))


def int_forward_mlp(net, x):
    """Exact integer semantics: ReLU, then argmax with the first maximum winning."""
    hid = np.maximum(0, x @ net["Q1"].T + net["B1"])
    out = hid @ net["Q2"].T + net["B2"]
    return out.argmax(axis=1)  # numpy argmax returns the first maximum


def code_bits_mlp(net, n_configs):
    bits = math.log2(n_configs)
    parts = {}
    for name in ("Q1", "Q2"):
        b, counts = ternary_layer_bits(net[name])
        parts[name] = dict(bits=b, counts=counts)
        bits += b
    bias_bits = sum(signed_int_bits(int(z)) for name in ("B1", "B2") for z in net[name])
    parts["biases"] = bias_bits
    return bits + bias_bits, parts


class TernaryCNN(nn.Module):
    """Valid convolutions (kernel, stride, out channels) with ReLU, then a linear layer."""

    def __init__(self, convs, t, t_fc=None):
        super().__init__()
        self.convs, self.t = convs, t
        self.t_fc = t if t_fc is None else t_fc
        self.ws, self.bs = nn.ParameterList(), nn.ParameterList()
        cin, side = 1, 28
        for k, st, cout in convs:
            self.ws.append(nn.Parameter(torch.randn(cout, cin, k, k) / math.sqrt(cin * k * k)))
            self.bs.append(nn.Parameter(torch.zeros(cout)))
            cin, side = cout, (side - k) // st + 1
        self.flat = cin * side * side
        self.ws.append(nn.Parameter(torch.randn(10, self.flat) / math.sqrt(self.flat)))
        self.bs.append(nn.Parameter(torch.zeros(10)))

    def forward(self, x):
        for (k, st, _), w, b in zip(self.convs, self.ws, self.bs):
            q, a = ternarize(w, self.t)
            x = F.relu(F.conv2d(x, a * q, b, stride=st))
        q, a = ternarize(self.ws[-1], self.t_fc)
        return x.flatten(1) @ (a * q).T + self.bs[-1]

    def integer_net(self, scale_in):
        layers, s = [], 1.0 / scale_in
        with torch.no_grad():
            for i, (w, b) in enumerate(zip(self.ws, self.bs)):
                q, a = ternarize(w, self.t_fc if i == len(self.ws) - 1 else self.t)
                s = s * a.item()
                layers.append(dict(Q=q.detach().cpu().numpy().astype(np.int64),
                                   B=torch.round(b / s).detach().cpu().numpy().astype(np.int64)))
        return dict(layers=layers, convs=self.convs)


def int_forward_cnn(net, x, batch=4000):
    """Exact integer semantics, evaluated in float64: all values stay below 2^50."""
    preds = []
    for i in range(0, len(x), batch):
        h = torch.tensor(x[i:i + batch], dtype=torch.float64).unsqueeze(1)
        for (k, st, _), L in zip(net["convs"], net["layers"]):
            h = F.conv2d(h, torch.tensor(L["Q"], dtype=torch.float64),
                         torch.tensor(L["B"], dtype=torch.float64), stride=st).clamp(min=0)
        L = net["layers"][-1]
        out = h.flatten(1) @ torch.tensor(L["Q"], dtype=torch.float64).T + torch.tensor(L["B"], dtype=torch.float64)
        assert out.abs().max().item() < 2 ** 50 and torch.equal(out, out.round())
        preds.append(out.argmax(dim=1).numpy())  # first maximum wins
    return np.concatenate(preds)


def code_bits_cnn(net, n_configs):
    bits, parts = math.log2(n_configs), []
    for L in net["layers"]:
        b, counts = ternary_layer_bits(L["Q"])
        bb = sum(signed_int_bits(int(z)) for z in L["B"])
        parts.append(dict(bits=b, counts=counts, bias_bits=bb))
        bits += b + bb
    return bits, parts


# ---------------------------------------------------------------- configs

CONFIGS = {}
for pool_k in (2, 4):
    for h in (16, 32, 64):
        for t in (0.7, 1.4):
            CONFIGS[f"mlp_p{pool_k}_h{h}_t{t}"] = dict(kind="mlp", pool=pool_k, hidden=h, t=t)
for name, convs in (("c4-8", ((5, 2, 4), (3, 2, 8))), ("c8-16", ((5, 2, 8), (3, 2, 16))),
                    ("c8-16-16", ((5, 2, 8), (3, 2, 16), (3, 1, 16))), ("c16-16-16", ((5, 2, 16), (3, 2, 16), (3, 1, 16)))):
    for t in (0.7, 1.4):
        CONFIGS[f"cnn_{name}_t{t}"] = dict(kind="cnn", convs=convs, t=t)
# Second grid, declared after seeing the first: separate threshold for the linear
# layer, 40 epochs, two seeds. Every config of both grids is charged.
for name, convs in (("c4-8", ((5, 2, 4), (3, 2, 8))), ("c6-12", ((5, 2, 6), (3, 2, 12))),
                    ("c8-16", ((5, 2, 8), (3, 2, 16))), ("c4-8-8", ((5, 2, 4), (3, 2, 8), (3, 1, 8))),
                    ("c8-16-16", ((5, 2, 8), (3, 2, 16), (3, 1, 16)))):
    for t in (0.5, 0.7, 1.0):
        for t_fc in (0.7, 1.0, 1.4):
            for seed in (0, 1):
                CONFIGS[f"cnn2_{name}_t{t}_f{t_fc}_s{seed}"] = dict(
                    kind="cnn", convs=convs, t=t, t_fc=t_fc, seed=seed, epochs=40)


def train_mlp(cfg, xtr, ytr, device, epochs=20, seed=0):
    torch.manual_seed(seed)
    k = cfg["pool"]
    scale_in = 255.0 * k * k
    xi = pool(xtr, k).reshape(len(xtr), -1)
    X = torch.tensor(xi / scale_in, dtype=torch.float32, device=device)
    Y = torch.tensor(ytr, device=device)
    model = TernaryMLP(X.shape[1], cfg["hidden"], cfg["t"]).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=3e-3)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, epochs)
    n = len(X)
    for _ in range(epochs):
        perm = torch.randperm(n, device=device)
        for i in range(0, n, 256):
            idx = perm[i:i + 256]
            loss = F.cross_entropy(model(X[idx]), Y[idx])
            opt.zero_grad()
            loss.backward()
            opt.step()
        sched.step()
    return model.integer_net(scale_in), xi


def train_cnn(cfg, xtr, ytr, device, epochs=20, seed=0):
    seed, epochs = cfg.get("seed", seed), cfg.get("epochs", epochs)
    torch.manual_seed(seed)
    X = torch.tensor(xtr / 255.0, dtype=torch.float32, device=device).unsqueeze(1)
    Y = torch.tensor(ytr, device=device)
    model = TernaryCNN(cfg["convs"], cfg["t"], cfg.get("t_fc")).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=3e-3)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, epochs)
    for _ in range(epochs):
        perm = torch.randperm(len(X), device=device)
        for i in range(0, len(X), 256):
            idx = perm[i:i + 256]
            loss = F.cross_entropy(model(X[idx]), Y[idx])
            opt.zero_grad()
            loss.backward()
            opt.step()
        sched.step()
    return model.integer_net(255.0)


def evaluate(name, cfg, xtr, ytr, xte, yte, device, epochs):
    if cfg["kind"] == "mlp":
        net, xi = train_mlp(cfg, xtr, ytr, device, epochs)
        k_train = int((int_forward_mlp(net, xi) != ytr).sum())
        k_test = int((int_forward_mlp(net, pool(xte, cfg["pool"]).reshape(len(xte), -1)) != yte).sum())
        bits, parts = code_bits_mlp(net, len(CONFIGS))
        params = sum(int(v.size) for v in net.values())
    else:
        net = train_cnn(cfg, xtr, ytr, device, epochs)
        k_train = int((int_forward_cnn(net, xtr) != ytr).sum())
        k_test = int((int_forward_cnn(net, xte) != yte).sum())
        bits, parts = code_bits_cnn(net, len(CONFIGS))
        params = sum(int(L["Q"].size + L["B"].size) for L in net["layers"])
    return net, k_train, k_test, bits, parts, params


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("mnist_dir")
    ap.add_argument("out_json")
    ap.add_argument("--configs", default=",".join(CONFIGS))
    ap.add_argument("--epochs", type=int, default=20)
    args = ap.parse_args()
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    xtr, ytr, xte, yte = load_mnist(args.mnist_dir)
    n = len(xtr)
    results = []
    for name in args.configs.split(","):
        cfg = CONFIGS[name]
        t0 = time.time()
        net, k_train, k_test, bits, parts, params = evaluate(name, cfg, xtr, ytr, xte, yte, device, args.epochs)
        r = dict(name=name, cfg=cfg, params=params,
                 train_errors=k_train, train_err=k_train / n, test_err=k_test / len(xte),
                 bits=bits, parts=parts,
                 bound_binomial_occam=binomial_occam(n, k_train, bits),
                 bound_kl_occam=kl_occam(n, k_train, bits), seconds=time.time() - t0)
        results.append(r)
        print(f"{name:22s} params={r['params']:6d} bits={bits:8.0f} train={r['train_err']:.4f} "
              f"test={r['test_err']:.4f} bound={r['bound_binomial_occam']:.4f} "
              f"(kl {r['bound_kl_occam']:.4f})", flush=True)
    Path(args.out_json).write_text(json.dumps(dict(n=n, delta=DELTA, n_configs=len(CONFIGS),
                                                   results=results), indent=1))


if __name__ == "__main__":
    main()
