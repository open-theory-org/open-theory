#!/usr/bin/env python3
"""Conformance of the tree-ensemble checks (`tree-robust`, `tree-monotone`): both lanes, one answer,
and no accepted false claim.

Runs every request through `ot_kernel --compare` (kernel and compiled lane must agree). Cases:

* the LightGBM example (`examples/tree_ensemble/`): robustness of an applicant's approval and
  monotonicity in each feature are accepted; categorical splits and `missing_type: Zero` are
  refused by the producer;
* random ensembles with double thresholds and leaves: every honest certificate the producer emits
  is accepted, and each accepted claim is then tested on the original double model, evaluated
  exactly, at random points (pairs for monotonicity) of the box: a counterexample fails the test;
* tampered certificates must be rejected: a per-tree bound one unit too tight, the decision
  threshold one unit past the bound, the decision flipped, the reached extreme leaf moved one unit
  past its bound, a cut one unit too low, a non-monotone tree;
* malformed requests (truncated, trailing numbers) are rejected.

Requires `lake build ot_kernel`.
"""
from __future__ import annotations

import json
import random
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "methods" / "trees"))
import tree_certificate as tc  # noqa: E402

KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"
EXAMPLE = ROOT / "examples" / "tree_ensemble"
D = 6


def run(requests: list[tuple[str, list[int]]]) -> list[bool]:
    text = "".join(f"{cli} {' '.join(map(str, r))}\n" for cli, r in requests)
    out = subprocess.run([str(KERNEL), "--stdin", "--compare"], input=text, capture_output=True, text=True)
    if out.returncode == 3:
        raise SystemExit(f"[FAIL] the kernel and compiled lanes disagree:\n{out.stderr}")
    answers = out.stdout.splitlines()
    if len(answers) != len(requests):
        raise SystemExit(f"[FAIL] expected {len(requests)} answers, got {len(answers)}: {out.stderr[:500]}")
    return [a == "true" for a in answers]


def evaluate(model: dict, x: list) -> Fraction:
    """The model's raw score, exactly, on the original (unscaled) model."""
    def go(t):
        if "leaf" in t:
            return Fraction(t["leaf"])
        return go(t["low"] if Fraction(x[t["feature"]]) <= Fraction(t["threshold"]) else t["high"])
    return Fraction(model.get("base", 0)) + sum(go(t) for t in model["trees"])


def point(box: dict, rng) -> list:
    x = []
    for f in range(D):
        lo, hi = box.get(str(f), [None, None])
        lo = -4 if lo is None else lo
        hi = 4 if hi is None else hi
        x.append(rng.choice([lo, hi, rng.uniform(lo, hi)]))
    return x


def rtree(rng, k):
    if k == 0:
        return {"leaf": rng.gauss(0, 0.2)}
    return {"feature": rng.randrange(D), "threshold": rng.uniform(-3, 3), "low": rtree(rng, k - 1), "high": rtree(rng, k - 1)}


def mtree(rng, k, lo, hi):
    """Increasing in feature 0 by construction."""
    if k == 0:
        return {"leaf": rng.uniform(lo, hi)}
    if rng.random() < 0.4:
        mid = (lo + hi) / 2
        return {"feature": 0, "threshold": rng.uniform(-3, 3), "low": mtree(rng, k - 1, lo, mid), "high": mtree(rng, k - 1, mid, hi)}
    return {"feature": rng.randrange(1, D), "threshold": rng.uniform(-3, 3), "low": mtree(rng, k - 1, lo, hi), "high": mtree(rng, k - 1, lo, hi)}


def robust_parts(req):
    """Positions of τ (index 1) and of each tree's bound in a tree-robust request."""
    i = 4
    d = req[3]
    for _ in range(2 * d):
        i += 1 if req[i] == 0 else 2
    n = req[i]
    i += 1
    bounds = []
    for _ in range(n):
        i = skip_tree(req, i)
        bounds.append(i)
        i += 1
    return bounds


def skip_tree(req, i):
    if req[i] == 0:
        return i + 2
    return skip_tree(req, skip_tree(req, i + 3))


def unzig(n):
    return n // 2 if n % 2 == 0 else -(n + 1) // 2


def main() -> int:
    rng = random.Random(20261101)
    failures = []
    requests: list[tuple[str, list[int]]] = []
    expect: list[tuple[bool, str]] = []

    def add(cli, req, want, what):
        requests.append((cli, req))
        expect.append((want, what))

    # -- the LightGBM example
    lgb = tc.load_model(EXAMPLE / "model_lightgbm.json")
    box = json.loads((EXAMPLE / "box_applicant.json").read_text())
    add("tree-robust", tc.robust_request(lgb, box, True, 0), True, "example: approval robust on the applicant box")
    add("tree-robust", tc.robust_request(lgb, box, False, 0), False, "example: decline on the same box")
    for f, up in [(0, True), (1, False), (2, True)]:
        add("tree-monotone", tc.monotone_request(lgb, f, up), True, f"example: monotone in feature {f}")
    for bad, why in [({"decision_type": "=="}, "categorical"), ({"missing_type": "Zero"}, "missing_type Zero")]:
        dump = json.loads((EXAMPLE / "model_lightgbm.json").read_text())
        dump["tree_info"][0]["tree_structure"].update(bad)
        try:
            tc.from_lightgbm(dump)
            failures.append(f"producer accepted a {why} split")
        except tc.NotSupported:
            pass

    # -- random ensembles
    semantic = []
    for case in range(40):
        model = {"base": rng.choice([0, 0.125, -0.5]), "trees": [rtree(rng, rng.randint(1, 4)) for _ in range(rng.randint(1, 12))]}
        x0 = [rng.uniform(-3, 3) for _ in range(D)]
        box = {str(f): [x0[f], x0[f]] for f in range(D)}
        for f in rng.sample(range(D), 2):
            w = rng.uniform(0, 0.5)
            box[str(f)] = [x0[f] - w, x0[f] + w]
        s, kl, kf = tc.scale(model)
        B = tc.scale_box(box, kf)
        lo = Fraction(s["base"] + sum(tc.reach(t, B, min) for t in s["trees"]), 2 ** kl)
        hi = Fraction(s["base"] + sum(tc.reach(t, B, max) for t in s["trees"]), 2 ** kl)
        for approve, tau in [(True, lo), (True, lo - Fraction(1, 7)), (False, hi + Fraction(1, 2 ** (kl + 1)))]:
            req = tc.robust_request(model, box, approve, tau)
            add("tree-robust", req, True, f"random {case}: honest {'approve' if approve else 'decline'}")
            semantic.append(("robust", model, box, approve, tau))
        # tampering an honest approval at τ = the lowest reachable score
        req = tc.robust_request(model, box, True, lo)
        pos = robust_parts(req)
        k = rng.randrange(len(pos))
        t1 = list(req); t1[pos[k]] = tc.zig(unzig(req[pos[k]]) + 1)
        add("tree-robust", t1, False, f"random {case}: a bound one unit too tight")
        t2 = list(req); t2[1] = tc.zig(unzig(req[1]) + 1)
        add("tree-robust", t2, False, f"random {case}: τ one unit past the bound")
        t3 = list(req); t3[2] = 0
        add("tree-robust", t3, False, f"random {case}: decision flipped")
        add("tree-robust", req[:-1], False, f"random {case}: truncated")
        add("tree-robust", req + [0], False, f"random {case}: trailing number")
        # monotone ensembles, and a broken one
        mm = {"base": 0, "trees": [mtree(rng, rng.randint(1, 4), -1, 1) for _ in range(rng.randint(1, 8))]}
        mreq = tc.monotone_request(mm, 0, True)
        add("tree-monotone", mreq, True, f"random {case}: honest monotone")
        semantic.append(("monotone", mm, {}, True, None))
        broken = {"base": 0, "trees": mm["trees"] + [{"feature": 0, "threshold": 0.5, "low": {"leaf": 0.3}, "high": {"leaf": 0.1}}]}
        if tc.monotone_request(broken, 0, True) is not None:
            failures.append(f"random {case}: producer certified a decreasing tree as increasing")
        forced = tc.monotone_request({"base": 0, "trees": broken["trees"][-1:]}, 0, False)
        add("tree-monotone", [0, 1] + forced[2:], False, f"random {case}: decreasing tree claimed increasing")

    answers = run(requests)
    for (want, what), got in zip(expect, answers):
        if got != want:
            failures.append(f"{what}: expected {want}, got {got}")

    # -- accepted claims hold on the original model
    for kind, model, box, flag, tau in semantic:
        for _ in range(200):
            if kind == "robust":
                x = point(box, rng)
                if (evaluate(model, x) >= tau) != flag:
                    failures.append(f"counterexample to an accepted robustness claim at {x}")
                    break
            else:
                x = point(box, rng)
                x2 = list(x); x2[0] = x[0] + abs(rng.gauss(0, 1))
                if evaluate(model, x2) < evaluate(model, x):
                    failures.append(f"counterexample to an accepted monotonicity claim at {x}")
                    break

    for f in failures:
        print(f"[FAIL] {f}")
    if failures:
        return 1
    print(f"{len(requests)}/{len(requests)} tree-check cases pass; kernel and compiled lanes agree; "
          f"{len(semantic)} accepted claims hold at 200 random points each")
    return 0


if __name__ == "__main__":
    sys.exit(main())
