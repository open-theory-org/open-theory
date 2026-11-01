#!/usr/bin/env python3
"""Robustness and monotonicity certificates for tree ensembles (untrusted producer).

Reads a tree ensemble (a LightGBM `Booster.dump_model()` JSON [@ke2017lightgbm], or the plain
format below), scales it exactly to integers, computes the witnesses and writes the request that
`ot_kernel` checks against `OpenTheory.Checks.Tree.robustCertK` / `monotoneCertK`. What an accepted
request means is proved once in Lean (`treeRobust_sound`, `treeMonotone_sound`); nothing here is
trusted: a wrong witness or a wrong scaling makes the kernel reject, or certifies a model whose
hash differs from the one deployed (A3).

Plain format: {"base": b, "trees": [tree, ...]}, a tree being {"leaf": v} or
{"feature": f, "threshold": t, "low": tree, "high": tree}, where an input goes `low` when
x[f] <= t (the LightGBM and XGBoost [@chen2016xgboost] convention). A box is
{"f": [lo, hi], ...} with `null` for an open end; missing features are unbounded.

Exact scaling. Thresholds and leaves are doubles, hence dyadic rationals: each feature is multiplied
by the least power of two that makes its thresholds integers, and the leaves and the decision
threshold by one power of two. Box bounds are rounded outwards, so the scaled box contains the
original one and a certificate for it covers the original box.

    python3 methods/trees/tree_certificate.py robust MODEL BOX --approve|--decline [--tau T]
    python3 methods/trees/tree_certificate.py monotone MODEL FEATURE --up|--down [--box BOX]
      prints the request (one line, for `ot_kernel --stdin`); --check also runs ot_kernel
"""
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class NotSupported(ValueError):
    pass


# ---------------------------------------------------------------- reading models

def from_lightgbm(dump: dict) -> dict:
    """The plain format of a LightGBM `dump_model()`; the initial score is in the first tree."""
    def node(n):
        if "leaf_value" in n:
            return {"leaf": n["leaf_value"]}
        if n.get("decision_type", "<=") != "<=":
            raise NotSupported(f"categorical split (decision_type {n['decision_type']!r})")
        if n.get("missing_type", "None") == "Zero":
            raise NotSupported("missing_type Zero routes x = 0 by default_left, not by the threshold")
        return {"feature": n["split_feature"], "threshold": n["threshold"],
                "low": node(n["left_child"]), "high": node(n["right_child"])}
    if dump.get("num_class", 1) != 1:
        raise NotSupported("multiclass model")
    return {"base": 0, "trees": [node(t["tree_structure"]) for t in dump["tree_info"]]}


def load_model(path: Path) -> dict:
    m = json.loads(path.read_text())
    return from_lightgbm(m) if "tree_info" in m else m


# ---------------------------------------------------------------- exact scaling

def pow2_denominator(x: Fraction) -> int:
    d = x.denominator
    if d & (d - 1):
        raise NotSupported(f"{x} is not a dyadic rational")
    return d.bit_length() - 1


def thresholds(t: dict, out: dict) -> None:
    if "leaf" not in t:
        out.setdefault(t["feature"], []).append(Fraction(t["threshold"]))
        thresholds(t["low"], out)
        thresholds(t["high"], out)


def leaves(t: dict, out: list) -> None:
    if "leaf" in t:
        out.append(Fraction(t["leaf"]))
    else:
        leaves(t["low"], out)
        leaves(t["high"], out)


def scale(model: dict) -> tuple[dict, int, list]:
    """Integer trees, the leaf scale exponent, and per-feature scale exponents."""
    ths: dict[int, list] = {}
    lvs: list = [Fraction(model.get("base", 0))]
    for t in model["trees"]:
        thresholds(t, ths)
        leaves(t, lvs)
    kf = {f: max(pow2_denominator(x) for x in xs) for f, xs in ths.items()}
    kl = max(pow2_denominator(x) for x in lvs)

    def go(t):
        if "leaf" in t:
            return ("leaf", int(Fraction(t["leaf"]) * 2 ** kl))
        f = t["feature"]
        return ("node", f, int(Fraction(t["threshold"]) * 2 ** kf[f]), go(t["low"]), go(t["high"]))
    return {"base": int(Fraction(model.get("base", 0)) * 2 ** kl), "trees": [go(t) for t in model["trees"]]}, kl, kf


def scale_box(box: dict, kf: dict) -> list:
    """Per feature (lo, hi), rounded outwards; a feature with no threshold needs no bound."""
    d = 1 + max([int(f) for f in box] + list(kf) + [-1])
    out = [(None, None)] * d
    for f, (lo, hi) in box.items():
        f = int(f)
        k = kf.get(f, 0)
        out[f] = (None if lo is None else math.floor(Fraction(lo) * 2 ** k),
                  None if hi is None else math.ceil(Fraction(hi) * 2 ** k))
    return out


# ---------------------------------------------------------------- witnesses (mirror Checks/Tree.lean)

def low_ok(B, f, t):
    lo = B[f][0] if f < len(B) else None
    return lo is None or lo <= t


def high_ok(B, f, t):
    hi = B[f][1] if f < len(B) else None
    return hi is None or t < hi


def reach(t, B, pick):
    """`pick` (min or max) of the leaves a point of the box reaches, each split tested on B."""
    if t[0] == "leaf":
        return t[1]
    _, f, th, l, r = t
    vals = ([reach(l, B, pick)] if low_ok(B, f, th) else []) + ([reach(r, B, pick)] if high_ok(B, f, th) else [])
    return pick(vals) if vals else reach(r, B, pick)


def cuts(t, B, j, up):
    """Cuts for `Tree.monoCut`, or None when the per-tree condition fails."""
    if t[0] == "leaf":
        return ("none",)
    _, f, th, l, r = t
    lo, hi = low_ok(B, f, th), high_ok(B, f, th)
    cl, cr = cuts(l, B, j, up), cuts(r, B, j, up)
    if (lo and cl is None) or (hi and cr is None):
        return None
    c = 0
    if f == j and lo and hi:
        a, b = (reach(l, B, max), reach(r, B, min)) if up else (reach(r, B, max), reach(l, B, min))
        if a > b:
            return None
        c = a if up else b
    return ("cut", c, cl or ("none",), cr or ("none",))


# ---------------------------------------------------------------- encoding (Checks/Tree.lean, "Requests")

def zig(z: int) -> int:
    return 2 * z if z >= 0 else -2 * z - 1


def enc_box(B) -> list:
    out = [len(B)]
    for lo, hi in B:
        out += [0] if lo is None else [1, zig(lo)]
        out += [0] if hi is None else [1, zig(hi)]
    return out


def enc_tree(t) -> list:
    if t[0] == "leaf":
        return [0, zig(t[1])]
    _, f, th, l, r = t
    return [1, f, zig(th)] + enc_tree(l) + enc_tree(r)


def enc_cuts(c) -> list:
    return [0] if c[0] == "none" else [1, zig(c[1])] + enc_cuts(c[2]) + enc_cuts(c[3])


def robust_request(model: dict, box: dict, approve: bool, tau) -> list[int]:
    s, kl, kf = scale(model)
    B = scale_box(box, kf)
    tau_s = math.ceil(Fraction(tau) * 2 ** kl)   # τ ≤ score ⇔ ⌈τ·2^kl⌉ ≤ score·2^kl
    ms = [reach(t, B, min if approve else max) for t in s["trees"]]
    req = [zig(s["base"]), zig(tau_s), int(approve)] + enc_box(B) + [len(ms)]
    for t, m in zip(s["trees"], ms):
        req += enc_tree(t) + [zig(m)]
    return req


def monotone_request(model: dict, feature: int, up: bool, box: dict | None = None) -> list[int] | None:
    s, _, kf = scale(model)
    B = scale_box(box or {}, kf)
    cs = [cuts(t, B, feature, up) for t in s["trees"]]
    if any(c is None for c in cs):
        return None
    req = [feature, int(up)] + enc_box(B) + [len(cs)]
    for t, c in zip(s["trees"], cs):
        req += enc_tree(t) + enc_cuts(c)
    return req


def ot_kernel(cli: str, req: list[int], time: bool = False) -> tuple[bool, str]:
    exe = ROOT / ".lake/build/bin/ot_kernel"
    args = [str(exe), "--stdin"] + (["--time"] if time else [])
    out = subprocess.run(args, input=f"{cli} {' '.join(map(str, req))}\n", capture_output=True, text=True)
    return out.stdout.strip() == "true", out.stderr.strip()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("robust")
    r.add_argument("model", type=Path)
    r.add_argument("box", type=Path)
    g = r.add_mutually_exclusive_group(required=True)
    g.add_argument("--approve", action="store_true")
    g.add_argument("--decline", action="store_true")
    r.add_argument("--tau", default="0", help="decision threshold on the raw score (logit of the probability cut)")
    m = sub.add_parser("monotone")
    m.add_argument("model", type=Path)
    m.add_argument("feature", type=int)
    g = m.add_mutually_exclusive_group(required=True)
    g.add_argument("--up", action="store_true")
    g.add_argument("--down", action="store_true")
    m.add_argument("--box", type=Path)
    for p in (r, m):
        p.add_argument("--check", action="store_true", help="run ot_kernel on the request")
    a = ap.parse_args()
    model = load_model(a.model)
    if a.cmd == "robust":
        cli, req = "tree-robust", robust_request(model, json.loads(a.box.read_text()), a.approve, a.tau)
    else:
        cli = "tree-monotone"
        req = monotone_request(model, a.feature, a.up, json.loads(a.box.read_text()) if a.box else None)
        if req is None:
            print("not certifiable: some tree is not monotone on the box (sufficient condition)", file=sys.stderr)
            return 1
    if a.check:
        ok, log = ot_kernel(cli, req, time=True)
        print(log, file=sys.stderr)
        return 0 if ok else 1
    print(cli, *req)
    return 0


if __name__ == "__main__":
    sys.exit(main())
