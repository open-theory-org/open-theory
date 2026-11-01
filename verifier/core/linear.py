"""Linear and logistic-regression models for the cards `robust-decision` and `monotone-feature` v0.1.

The model file (`subject.model`) is {"intercept": b, "coef": [w_0, …]} (scikit-learn's
`LogisticRegression.intercept_[0]`, `coef_[0]`), and the claim gives the decision threshold either
on the score (`tau`) or, for a logistic regression, on the probability (`probability`: approve when
σ(score) ≥ p, that is when score ≥ log(p / (1 − p))). The verifier

  1. checks the model's digest,
  2. translates the model exactly to integers (assumption A11): the weights and the intercept are
     doubles, hence dyadic, scaled by `2^kw`; the box bounds are rounded outwards to multiples of
     `2^-KX`; the threshold, times `2^(kw + KX)`, is rounded up for an approval and down for a
     decline, so that the integer model's decision implies the deployed model's (a real score is
     not an integer, unlike a tree's),
  3. encodes the request and has the Lean kernel evaluate `Checks.Linear.robust` / `monotone`,
     after checking that the Lean decoder reads it as the claim (`ot_kernel --show`).

When every feature is bounded, robustness goes through the packed check instead
(`linear-robust-packed`, `Checks.Linear.robustPackedN`): the weights, split into their positive and
negative parts, and the box bounds, shifted by `O` to be non-negative and reversed, are packed as
base-2^B digits, and two big-integer products give the four dot products the corner bounds need
(Kronecker substitution, docs/fast-certificates.md). Its cost does not grow with the number of
features. `ClaimTypes.linearRobustPacked` states what it proves, about the model and the box the
request stores; the verifier builds both from the claim, and `--show` checks the threshold, the
decision and the sizes.

`ClaimTypes.linearRobust` / `linearRobustPacked` / `linearMonotone` turn an accepted check into the
claim, with `δ = 0`.
"""
from __future__ import annotations

import math
from decimal import Decimal, getcontext
from fractions import Fraction

from .engine import Reject, require
from .heldout_error import Task
from .trees import NotSupported, enc_box, exact, pow2_denominator, show_box, zig

KX = 64            # inputs are read on a grid of 2^-64
LOGIT_DIGITS = 60  # decimal digits of log(p / (1 − p)); the bound is widened by 10^-50


def parse_model(model: dict) -> tuple[Fraction, list[Fraction]]:
    if not isinstance(model, dict) or "coef" not in model:
        raise NotSupported("a linear model is {\"intercept\": b, \"coef\": [w, …]}")
    coef = model["coef"]
    if coef and isinstance(coef[0], list):        # scikit-learn's coef_ for a binary model is 1 × d
        if len(coef) != 1:
            raise NotSupported("multiclass linear model")
        coef = coef[0]
    b = model.get("intercept", 0)
    b = b[0] if isinstance(b, list) else b
    return Fraction(b), [Fraction(w) for w in coef]


def logit_bound(p: Fraction, up: bool) -> Fraction:
    """A rational at least (up) or at most (down) log(p / (1 − p))."""
    if not 0 < p < 1:
        raise Reject("claim.probability must be in (0, 1)")
    getcontext().prec = LOGIT_DIGITS
    v = (Decimal(p.numerator) / Decimal(p.denominator - p.numerator)).ln()
    margin = Fraction(1, 10 ** 50)
    return Fraction(v) + margin if up else Fraction(v) - margin


def threshold(claim: dict, approve: bool) -> tuple[Fraction, str]:
    if "probability" in claim:
        p = exact(claim["probability"])
        return logit_bound(p, up=approve), f"probability ≥ {claim['probability']}"
    tau = claim.get("tau", "0")
    return exact(tau), f"score ≥ {tau}"


def scaled(model: dict, box: dict, tau: Fraction, approve: bool):
    b, ws = parse_model(model)
    kw = max(pow2_denominator(x) for x in [b, *ws])
    K = kw + KX
    W = [int(w * 2 ** kw) for w in ws]
    bias = int(b * 2 ** K)
    t = tau * 2 ** K
    T = math.ceil(t) if approve else math.floor(t)
    d = 1 + max([int(f) for f in box] + [len(W) - 1, -1])
    B = [(None, None)] * d
    for f, (lo, hi) in box.items():
        B[int(f)] = (None if lo is None else math.floor(exact(lo) * 2 ** KX),
                     None if hi is None else math.ceil(exact(hi) * 2 ** KX))
    return bias, T, W, B


def robust_request(model: dict, box: dict, approve: bool, tau: Fraction) -> tuple[list[int], str]:
    bias, T, W, B = scaled(model, box, tau, approve)
    req = [zig(bias), zig(T), int(approve)] + enc_box(B) + [len(W)] + [zig(w) for w in W]
    show = f"bias={bias} tau={T} approve={'true' if approve else 'false'} box=[{show_box(B)}] weights={len(W)}"
    return req, show


def pack(digits: list[int], B: int) -> int:
    """Σ digits[j] · 2^(B j): slot j of the result is digits[j] (`Slots.slot`)."""
    out = 0
    for v in reversed(digits):
        out = (out << B) | v
    return out


def robust_packed_request(model: dict, box: dict, approve: bool, tau: Fraction):
    """The `linear-robust-packed` request, or None when some feature is unbounded."""
    bias, T, W, Bx = scaled(model, box, tau, approve)
    d = len(Bx)
    W = W + [0] * (d - len(W))
    if d == 0 or any(lo is None or hi is None for lo, hi in Bx):
        return None
    O = max([0] + [-lo for lo, _ in Bx] + [-hi for _, hi in Bx])
    Wp, Wm = [max(w, 0) for w in W], [max(-w, 0) for w in W]
    L = [lo + O for lo, _ in reversed(Bx)]
    H = [hi + O for _, hi in reversed(Bx)]
    mW = max(v.bit_length() for v in Wp + Wm)
    mL = max(v.bit_length() for v in L + H)
    B = (d << (mW + mL)).bit_length() + 1           # d · 2^(mW + mL) < 2^B − 1
    req = [B, d, mW, mL, O, zig(bias), zig(T), pack(Wp, B), pack(Wm, B), pack(L, B), pack(H, B), int(approve)]
    show = (f"bias={bias} tau={T} approve={'true' if approve else 'false'} features={d} slot={B} "
            f"offset={O} weightBits={mW} boundBits={mL}")
    return req, show


def monotone_request(model: dict, feature: int, up: bool) -> tuple[list[int], str]:
    _, ws = parse_model(model)
    kw = max([pow2_denominator(x) for x in ws] + [0])
    W = [int(w * 2 ** kw) for w in ws]
    req = [feature, int(up), len(W)] + [zig(w) for w in W]
    return req, f"feature={feature} up={'true' if up else 'false'} weights={len(W)}"


TRUSTED = [
    "statements of OpenTheory.ClaimTypes.linearRobust / linearRobustPacked / linearMonotone (Specs/ClaimTypes.lean)",
    "this verifier's translation of the model file to the integer model (verifier/core/linear.py): A11, "
    "and for the packed check its packing of the weights and the box into slots",
    "ot_kernel's construction of the kernel's proposition from the request, cross-checked against the "
    "claim with `ot_kernel --show`",
]
NOT_COVERED = [
    "inputs outside the box; preprocessing before the model (scaling, encoding)",
    "whether the model file is the deployed model (A3)",
]


def robust_task(model: dict, digest: str, claim: dict, box: dict) -> Task:
    decision = require(claim, "decision", str, "claim")
    if decision not in ("approve", "decline"):
        raise Reject("claim.decision must be 'approve' or 'decline'")
    approve = decision == "approve"
    try:
        tau, how = threshold(claim, approve)
        packed = robust_packed_request(model, box, approve, tau)
        req, show = packed or robust_request(model, box, approve, tau)
    except NotSupported as e:
        raise Reject(f"model not supported: {e}")
    if packed:
        cli, call, meaning = ("linear-robust-packed", "Checks.Linear.robustPackedN …",
            "ClaimTypes.linearRobustPacked (linearRobustPacked_sound): the decision is the claimed one on every "
            "input of the box the request stores, δ = 0; the verifier packed that box and model from the claim")
    else:
        cli, call, meaning = ("linear-robust", "Checks.Linear.robust …",
            "ClaimTypes.linearRobust (linearRobust_sound): the decision is the claimed one on every "
            "input of the box, δ = 0 (the check is exact: a linear score is extreme at a corner)")
    n = len(parse_model(model)[1])
    bounded = ", ".join(f"x{f} ∈ [{lo}, {hi}]" for f, (lo, hi) in sorted(box.items(), key=lambda kv: int(kv[0])))
    return Task(
        lean="", theorem="", guarantee="linear-robust-model", delta="0",
        words=(f"The linear model sha256:{digest[:16]}… ({n} features) "
               f"{'approves' if approve else 'declines'} ({how} approves) every input with "
               f"{bounded or 'any features'}; features not listed are unbounded."),
        checked=[f"model digest sha256:{digest}",
                 "exact integer translation of the model, threshold rounded towards the claim (A11)",
                 f"the Lean decoder reads the request as: {show}"],
        trusted=TRUSTED, does_not_cover=NOT_COVERED,
        fast=[cli, *req], fast_call=call, fast_meaning=meaning,
        fast_explain=lambda: "some corner of the box is decided otherwise, or a feature with a non-zero weight "
                             "is unbounded",
        expect_show=show)


def monotone_task(model: dict, digest: str, claim: dict, feature: int, up: bool) -> Task:
    try:
        req, show = monotone_request(model, feature, up)
    except NotSupported as e:
        raise Reject(f"model not supported: {e}")
    return Task(
        lean="", theorem="", guarantee="linear-monotone-model", delta="0",
        words=(f"The score of the linear model sha256:{digest[:16]}… is "
               f"{'non-decreasing' if up else 'non-increasing'} in feature {feature} on all inputs, "
               "the other features fixed."),
        checked=[f"model digest sha256:{digest}", f"the Lean decoder reads the request as: {show}"],
        trusted=TRUSTED, does_not_cover=NOT_COVERED[:1] + NOT_COVERED[1:],
        fast=["linear-monotone", *req], fast_call="Checks.Linear.monotone …",
        fast_meaning="ClaimTypes.linearMonotone (linearMonotone_sound): raising the feature never moves the score "
                     "the other way, δ = 0",
        fast_explain=lambda: f"the weight of feature {feature} has the other sign",
        expect_show=show)
