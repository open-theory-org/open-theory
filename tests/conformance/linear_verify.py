#!/usr/bin/env python3
"""Conformance of the linear-model checks (`linear-robust`, `linear-robust-packed`, `linear-monotone`).

For random models with double coefficients and random boxes, the true least and greatest scores on
the box are computed exactly (at the corners), and:

* claims just inside them are accepted (approve with τ a little below the least score, decline with
  τ a little above the greatest; the same with a probability threshold), and every accepted claim is
  re-tested on the original model at random points of the box, in exact arithmetic;
* claims just outside them are **rejected**: the corner that breaks them lies in the box, so they are
  false;
* the packed request gives the same answers, and unpacking its slots (as `packedModel` and
  `packedBox` read them) gives back the integer model and box of the per-feature request;
* monotonicity is accepted exactly for the sign of the weight;
* every request runs in both lanes (`ot_kernel --compare`), and three bundles go through `ot verify`
  (accepted, a false claim, a model changed after its digest was taken).

Requires `lake build ot_kernel ot_check`.
"""
from __future__ import annotations

import json
import random
import subprocess
import sys
import tempfile
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from verifier.core import linear  # noqa: E402
from verifier.core.engine import verify  # noqa: E402

KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"
EPS = Fraction(1, 10 ** 6)


def score(model, x) -> Fraction:
    b, ws = linear.parse_model(model)
    return b + sum(w * Fraction(v) for w, v in zip(ws, x))


def extremes(model, box):
    b, ws = linear.parse_model(model)
    lo = hi = b
    for f, w in enumerate(ws):
        l, h = (Fraction(box[str(f)][0]), Fraction(box[str(f)][1]))
        lo += w * (l if w >= 0 else h)
        hi += w * (h if w >= 0 else l)
    return lo, hi


def sigmoid_ge(s: Fraction, p: Fraction) -> bool:
    getcontext().prec = 80
    return Decimal(s.numerator) / Decimal(s.denominator) >= (Decimal(p.numerator) / Decimal(p.denominator - p.numerator)).ln()


def run(reqs):
    text = "".join(" ".join(map(str, r)) + "\n" for r in reqs)
    out = subprocess.run([str(KERNEL), "--stdin", "--compare"], input=text, capture_output=True, text=True)
    if out.returncode == 3:
        raise SystemExit(f"[FAIL] lanes disagree:\n{out.stderr}")
    return [l == "true" for l in out.stdout.splitlines()]


def unpacked_ok(req, scaled, failures):
    """The packed request stores the integer model and box of `scaled` (mirror of `packedModel`, `packedBox`)."""
    B, d, _, _, O, zb, zt, Wp, Wm, LR, HR, c = req
    slot = lambda j, x: (x >> (B * j)) % (1 << B)
    unzig = lambda z: z // 2 if z % 2 == 0 else -(z + 1) // 2
    bias, T, W, Bx = scaled
    W = W + [0] * (d - len(W))
    if (unzig(zb), unzig(zt)) != (bias, T) or [slot(f, Wp) - slot(f, Wm) for f in range(d)] != W or \
            [(slot(d - 1 - f, LR) - O, slot(d - 1 - f, HR) - O) for f in range(d)] != list(Bx):
        failures.append(f"packed request does not store the model and box: {req[:7]}")


def main() -> int:
    rng = random.Random(11)
    reqs, want, what, semantic = [], [], [], []
    failures0: list[str] = []

    def add(req, w, s, sem=None):
        reqs.append(req); want.append(w); what.append(s); semantic.append(sem)

    for case in range(60):
        d = rng.randint(1, 30)
        model = {"intercept": rng.gauss(0, 1), "coef": [rng.choice([0.0, rng.gauss(0, 1)]) for _ in range(d)]}
        box = {}
        for f in range(d):
            c = rng.uniform(-5, 5)
            w = rng.choice([0, 0, rng.uniform(0, 1)])
            box[str(f)] = [str(Fraction(c - w).limit_denominator(1000)), str(Fraction(c + w).limit_denominator(1000))]
        lo, hi = extremes(model, box)
        for approve, tau, ok in ((True, lo - EPS, True), (True, lo + EPS, False), (False, hi + EPS, True), (False, hi - EPS, False)):
            req, _ = linear.robust_request(model, box, approve, tau)
            add(["linear-robust", *req], ok, f"{case}: {'approve' if approve else 'decline'} τ {'inside' if ok else 'outside'}",
                ("tau", model, box, approve, tau) if ok else None)
            preq, _ = linear.robust_packed_request(model, box, approve, tau)
            unpacked_ok(preq, linear.scaled(model, box, tau, approve), failures0)
            add(["linear-robust-packed", *preq], ok, f"{case}: packed {'approve' if approve else 'decline'} τ "
                f"{'inside' if ok else 'outside'}")
        p = Fraction(1, 2) + Fraction(rng.randint(-40, 40), 100)
        approve = sigmoid_ge(lo - EPS, p)
        if approve:
            req, _ = linear.robust_request(model, box, True, linear.logit_bound(p, up=True))
            add(["linear-robust", *req], True, f"{case}: approve at probability {p}", ("p", model, box, True, p))
        j = rng.randrange(d)
        w = linear.parse_model(model)[1][j]
        for up in (True, False):
            req, _ = linear.monotone_request(model, j, up)
            add(["linear-monotone", *req], (w >= 0) if up else (w <= 0), f"{case}: monotone {'up' if up else 'down'} (w = {float(w):.3g})")

    got = run(reqs)
    failures = failures0
    if len(got) != len(reqs):
        failures.append(f"expected {len(reqs)} answers, got {len(got)}")
    for s, w, g in zip(what, want, got):
        if w != g:
            failures.append(f"{s}: expected {w}, got {g}")
    checked = 0
    for g, sem in zip(got, semantic):
        if not g or sem is None:
            continue
        kind, model, box, approve, thr = sem
        for _ in range(100):
            x = [Fraction(rng.choice([box[str(f)][0], box[str(f)][1]])) if rng.random() < 0.5 else
                 Fraction(box[str(f)][0]) + (Fraction(box[str(f)][1]) - Fraction(box[str(f)][0])) * Fraction(rng.randint(0, 1000), 1000)
                 for f in range(len(box))]
            s = score(model, x)
            decided = (s >= thr) if kind == "tau" else sigmoid_ge(s, thr)
            if decided != approve:
                failures.append(f"counterexample to an accepted claim at {x}")
                break
        checked += 1

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        ex = ROOT / "examples" / "linear_model"
        prod = ROOT / "methods" / "linear" / "linear_certificate.py"
        def produce(name, *args):
            subprocess.run([sys.executable, str(prod), *args, "--out", str(tmp / name)], check=True, capture_output=True)
        produce("ok", "robust", str(ex / "model.json"), str(ex / "box_applicant.json"), "--approve", "--probability", "0.5")
        produce("false", "robust", str(ex / "model.json"), str(ex / "box_applicant.json"), "--decline", "--probability", "0.5")
        produce("tampered", "robust", str(ex / "model.json"), str(ex / "box_applicant.json"), "--approve", "--probability", "0.5")
        m = json.loads((tmp / "tampered" / "model.json").read_text()); m["coef"][1] = -30.0
        (tmp / "tampered" / "model.json").write_text(json.dumps(m))
        for name, ok in (("ok", True), ("false", False), ("tampered", False)):
            r = verify(tmp / name, timeout=120)
            if r.accepted != ok:
                failures.append(f"bundle {name}: expected {ok}, got {r.accepted} ({r.reason})")
            elif ok and "verified · kernel lane · δ = 0" not in r.summary():
                failures.append(f"bundle {name}: result line {r.summary()!r}")

    for f in failures:
        print(f"[FAIL] {f}")
    if failures:
        return 1
    print(f"{len(reqs)}/{len(reqs)} linear-check cases pass; kernel and compiled lanes agree; {checked} accepted "
          "claims hold at 100 random points each; 3/3 bundles through ot verify")
    return 0


if __name__ == "__main__":
    sys.exit(main())
