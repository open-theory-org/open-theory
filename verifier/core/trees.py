"""Claim cards `robust-decision` and `monotone-feature` v0.1, for tree ensembles
(specs/claims/robust-decision.md, monotone-feature.md).

The bundle holds the model (`subject.model`: a LightGBM `dump_model()` JSON [@ke2017lightgbm], or the plain format
below) and the claim. The verifier

  1. checks the model's digest,
  2. translates the model exactly to the integer ensemble of `OpenTheory.Checks.Tree` (this
     translation is assumption A11: doubles are dyadic, so each feature and the leaves are scaled by
     powers of two; categorical splits and `missing_type: Zero` are refused),
  3. computes the witnesses itself (a bound per tree, a cut per split: untrusted, the kernel checks
     them) and encodes the request,
  4. has the Lean kernel evaluate `robustCertK` / `monotoneCertK` on it (`ot_kernel`), after checking
     that the Lean decoder reads the request as the claim below (`ot_kernel --show`).

`ClaimTypes.treeRobust` / `treeMonotone` turn an accepted check into the claim, with `δ = 0`.

Plain model format: {"base": b, "trees": [tree, ...]}, a tree being {"leaf": v} or
{"feature": f, "threshold": t, "low": tree, "high": tree}; an input goes `low` when x[f] <= t.
A box is {"f": [lo, hi], ...}, bounds as decimal strings or numbers, `null` for an open end;
features left out are unbounded.
"""
from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

from .engine import Reject, require
from .heldout_error import Task


class NotSupported(ValueError):
    pass


# ---------------------------------------------------------------- reading models (A11)

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


def plain(model: dict) -> dict:
    return from_lightgbm(model) if "tree_info" in model else model


def exact(x) -> Fraction:
    """A number as written: decimal strings exactly; JSON numbers by their shortest decimal form."""
    if isinstance(x, (str, int, Fraction)):
        return Fraction(x)
    return Fraction(repr(x))


def pow2_denominator(x: Fraction) -> int:
    d = x.denominator
    if d & (d - 1):
        raise NotSupported(f"{x} is not a dyadic rational")
    return d.bit_length() - 1


def _thresholds(t, out):
    if "leaf" not in t:
        out.setdefault(t["feature"], []).append(Fraction(t["threshold"]))
        _thresholds(t["low"], out)
        _thresholds(t["high"], out)


def _leaves(t, out):
    if "leaf" in t:
        out.append(Fraction(t["leaf"]))
    else:
        _leaves(t["low"], out)
        _leaves(t["high"], out)


def scale(model: dict) -> tuple[dict, int, dict]:
    """Integer trees, the leaf scale exponent, and the per-feature scale exponents."""
    ths: dict[int, list] = {}
    lvs: list = [Fraction(model.get("base", 0))]
    for t in model["trees"]:
        _thresholds(t, ths)
        _leaves(t, lvs)
    kf = {f: max(pow2_denominator(x) for x in xs) for f, xs in ths.items()}
    kl = max(pow2_denominator(x) for x in lvs)

    def go(t):
        if "leaf" in t:
            return ("leaf", int(Fraction(t["leaf"]) * 2 ** kl))
        f = t["feature"]
        return ("node", f, int(Fraction(t["threshold"]) * 2 ** kf[f]), go(t["low"]), go(t["high"]))
    return {"base": int(Fraction(model.get("base", 0)) * 2 ** kl), "trees": [go(t) for t in model["trees"]]}, kl, kf


def scale_box(box: dict, kf: dict) -> list:
    """Per feature (lo, hi), rounded outwards: the scaled box contains the original one."""
    d = 1 + max([int(f) for f in box] + list(kf) + [-1])
    out = [(None, None)] * d
    for f, (lo, hi) in box.items():
        k = kf.get(int(f), 0)
        out[int(f)] = (None if lo is None else math.floor(exact(lo) * 2 ** k),
                       None if hi is None else math.ceil(exact(hi) * 2 ** k))
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


def show_box(B) -> str:
    """Mirror of `Checks.Tree.showBox`."""
    s = lambda v: "-" if v is None else str(v)
    return " ".join(f"{s(lo)}:{s(hi)}" for lo, hi in B)


def robust_request(model: dict, box: dict, approve: bool, tau) -> tuple[list[int], str]:
    """The `tree-robust` request and what the Lean decoder must read it as."""
    s, kl, kf = scale(model)
    B = scale_box(box, kf)
    tau_s = math.ceil(exact(tau) * 2 ** kl)   # τ ≤ score ⇔ ⌈τ·2^kl⌉ ≤ score·2^kl
    ms = [reach(t, B, min if approve else max) for t in s["trees"]]
    req = [zig(s["base"]), zig(tau_s), int(approve)] + enc_box(B) + [len(ms)]
    for t, m in zip(s["trees"], ms):
        req += enc_tree(t) + [zig(m)]
    show = f"base={s['base']} tau={tau_s} approve={'true' if approve else 'false'} box=[{show_box(B)}] trees={len(ms)}"
    return req, show


def monotone_request(model: dict, feature: int, up: bool, box: dict | None = None) -> tuple[list[int], str] | None:
    s, _, kf = scale(model)
    B = scale_box(box or {}, kf)
    cs = [cuts(t, B, feature, up) for t in s["trees"]]
    if any(c is None for c in cs):
        return None
    req = [feature, int(up)] + enc_box(B) + [len(cs)]
    for t, c in zip(s["trees"], cs):
        req += enc_tree(t) + enc_cuts(c)
    show = f"feature={feature} up={'true' if up else 'false'} box=[{show_box(B)}] trees={len(cs)}"
    return req, show


# ---------------------------------------------------------------- handlers

TRUSTED = [
    "statements of OpenTheory.ClaimTypes.treeRobust / treeMonotone (Specs/ClaimTypes.lean)",
    "this verifier's translation of the model file to the integer ensemble (verifier/core/trees.py): A11",
    "ot_kernel's construction of the kernel's proposition from the request, cross-checked against the "
    "claim with `ot_kernel --show`",
]
NOT_COVERED = [
    "inputs outside the box; inputs with missing values (NaN routing by default_left)",
    "preprocessing before the model (scaling, binning, one-hot encoding)",
    "whether the model file is the deployed model (A3)",
]


def load_model(bundle: Path, cert: dict, load_file) -> tuple[dict, str]:
    subject = require(cert, "subject", dict, "certificate")
    model_obj, digest = load_file(bundle, require(subject, "model", dict, "subject"), "subject.model")
    try:
        return plain(model_obj), digest
    except NotSupported as e:
        raise Reject(f"model not supported: {e}")
    except (KeyError, TypeError) as e:
        raise Reject(f"model is not a LightGBM dump nor the plain format ({e})")


def parse_box(claim: dict) -> dict:
    box = claim.get("box", {})
    if not isinstance(box, dict):
        raise Reject("claim.box must be an object {feature: [lo, hi]}")
    for f, b in box.items():
        if not f.isdigit() or not isinstance(b, list) or len(b) != 2:
            raise Reject(f"claim.box[{f!r}] must be a feature index with [lo, hi]")
        try:
            [None if v is None else exact(v) for v in b]
        except (ValueError, ZeroDivisionError):
            raise Reject(f"claim.box[{f!r}]: bounds must be numbers or decimal strings")
    return box


def handle_robust(bundle: Path, cert: dict, load_file) -> Task:
    claim = cert["claim"]
    if require(claim, "version", str, "claim") != "0.1":
        raise Reject("claim.version must be '0.1'")
    decision = require(claim, "decision", str, "claim")
    if decision not in ("approve", "decline"):
        raise Reject("claim.decision must be 'approve' or 'decline'")
    tau = claim.get("tau", "0")
    try:
        exact(tau)
    except (ValueError, ZeroDivisionError):
        raise Reject("claim.tau must be a number or a decimal string")
    box = parse_box(claim)
    model, digest = load_model(bundle, cert, load_file)
    try:
        req, show = robust_request(model, box, decision == "approve", tau)
    except NotSupported as e:
        raise Reject(f"model not supported: {e}")
    bounded = ", ".join(f"x{f} ∈ [{lo}, {hi}]" for f, (lo, hi) in sorted(box.items(), key=lambda kv: int(kv[0])))
    return Task(
        lean="", theorem="", guarantee="tree-robust-lightgbm", delta="0",
        words=(f"The tree ensemble sha256:{digest[:16]}… ({len(model['trees'])} trees) "
               f"{'approves' if decision == 'approve' else 'declines'} (raw score ≥ {tau} approves) every input "
               f"with {bounded or 'any features'}; features not listed are unbounded."),
        checked=[f"model digest sha256:{digest}",
                 "exact integer translation of the model (A11) and per-tree bounds (computed by the verifier)",
                 f"the Lean decoder reads the request as: {show}"],
        trusted=TRUSTED, does_not_cover=NOT_COVERED,
        fast=["tree-robust", *req], fast_call="Checks.Tree.robustCertK …",
        fast_meaning="ClaimTypes.treeRobust (treeRobust_sound): the decision is the claimed one on every input "
                     "of the box, δ = 0",
        fast_explain=lambda: "some input of the box may be decided otherwise (the check is sound, not complete: "
                             "trees sharing a feature cannot all reach their extreme leaves)",
        expect_show=show)


def handle_monotone(bundle: Path, cert: dict, load_file) -> Task:
    claim = cert["claim"]
    if require(claim, "version", str, "claim") != "0.1":
        raise Reject("claim.version must be '0.1'")
    feature = require(claim, "feature", int, "claim")
    direction = require(claim, "direction", str, "claim")
    if direction not in ("increasing", "decreasing") or feature < 0:
        raise Reject("claim.direction must be 'increasing' or 'decreasing', claim.feature ≥ 0")
    box = parse_box(claim)
    model, digest = load_model(bundle, cert, load_file)
    res = monotone_request(model, feature, direction == "increasing", box)
    if res is None:
        raise Reject(f"some tree is not monotone in feature {feature} on the box (the per-tree condition, "
                     "which suffices for the ensemble, fails)")
    req, show = res
    return Task(
        lean="", theorem="", guarantee="tree-monotone-lightgbm", delta="0",
        words=(f"The score of the tree ensemble sha256:{digest[:16]}… ({len(model['trees'])} trees) is "
               f"{'non-decreasing' if direction == 'increasing' else 'non-increasing'} in feature {feature}"
               f"{' on the box' if box else ' on all inputs'}, the other features fixed."),
        checked=[f"model digest sha256:{digest}",
                 "exact integer translation of the model (A11) and cuts per split (computed by the verifier)",
                 f"the Lean decoder reads the request as: {show}"],
        trusted=TRUSTED, does_not_cover=NOT_COVERED,
        fast=["tree-monotone", *req], fast_call="Checks.Tree.monotoneCertK …",
        fast_meaning="ClaimTypes.treeMonotone (treeMonotone_sound): raising the feature never moves the score "
                     "the other way, δ = 0",
        fast_explain=lambda: "a cut fails to separate the leaves of some split",
        expect_show=show)


# certificates name the claim card; a card serves several families, told apart by the subject
HANDLERS = {"robust-decision": handle_robust, "monotone-feature": handle_monotone}
