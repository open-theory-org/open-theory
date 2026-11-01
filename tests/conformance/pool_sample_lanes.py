#!/usr/bin/env python3
"""Conformance of `pool-sample` / `pool-sample-witness`: the kernel derives the sample itself.

Through `ot_kernel --compare` (kernel and compiled lanes must agree):

* honest requests (indices = block mod N, bits from the items' values) are accepted;
* rejected: an index that is not its block mod N; an item changed so that it fails, one failure
  more than the claimed count; a request with one position missing; `same` flipped, so the kernel
  counts the complement; a malformed request.

An item changed to hide a failure is not the kernel's to catch: the item is then not the committed
one, which the verifier's Merkle inclusion check rejects (A12-commitment-binding).

Requires `lake build ot_kernel`.
"""
from __future__ import annotations

import hashlib
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from verifier.core.pool_rate import sample_args  # noqa: E402

KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"


def run(reqs):
    text = "".join(" ".join(r) + "\n" for r in reqs)
    out = subprocess.run([str(KERNEL), "--stdin", "--compare"], input=text, capture_output=True, text=True)
    if out.returncode == 3:
        raise SystemExit(f"[FAIL] lanes disagree:\n{out.stderr}")
    return [l == "true" for l in out.stdout.splitlines()]


def main() -> int:
    rng = random.Random(7)
    reqs, want, what = [], [], []

    def add(r, w, s):
        reqs.append(r); want.append(w); what.append(s)

    for case in range(30):
        n = rng.choice([8, 40, 200])
        N = rng.choice([10, 1000, 99991])
        blocks = [int.from_bytes(hashlib.sha256(f"{case}/{i}".encode()).digest(), "big") for i in range(n)]
        pairs = [("ok" if rng.random() < 0.8 else "bad", "ok") for _ in range(n)]
        fails = sum(a != b for a, b in pairs)
        witness = (1, 2) if n == 200 else None
        part = (fails, 1, 2, witness)       # bound 1/2, δ = 1/2: loose enough to accept
        r = sample_args(blocks, N, pairs, False, part, 2)
        add(r, True, f"{case}: honest")
        head = 8 if witness is None else 10
        i = rng.randrange(n)
        t = list(r); t[head + 4 * i + 1] = str((blocks[i] + 1) % N)
        add(t, False, f"{case}: index is not block mod N")
        t = list(r); t[head + 4 * i + 2] = t[head + 4 * i + 3] if pairs[i][0] != pairs[i][1] else hex(int(t[head + 4 * i + 3], 16) + 1)
        tight = sample_args(blocks, N, pairs, False, (fails, 1, 2, witness), 2)
        t2 = list(tight); t2[head + 4 * i + 2] = t[head + 4 * i + 2]
        if pairs[i][0] == pairs[i][1]:
            add(t2, False, f"{case}: one failure more than the claimed count")
        add(r[:-4], False, f"{case}: one position missing")
        flipped = list(r); flipped[2] = "1"
        if fails != n - fails and (n - fails) > fails:
            add(flipped, False, f"{case}: counted the complement")
        add(r[:-1], False, f"{case}: malformed")
    got = run(reqs)
    failures = [f"{s}: expected {w}, got {g}" for s, w, g in zip(what, want, got) if w != g]
    if len(got) != len(reqs):
        failures.append(f"expected {len(reqs)} answers, got {len(got)}")
    for f in failures:
        print(f"[FAIL] {f}")
    if failures:
        return 1
    print(f"{len(reqs)}/{len(reqs)} pool-sample cases pass; kernel and compiled lanes agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
