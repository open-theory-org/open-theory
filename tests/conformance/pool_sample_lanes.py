#!/usr/bin/env python3
"""Conformance of `pool-sample`, `pool-sample-witness` and their packed forms: the kernel derives the
sample itself.

Through `ot_kernel --compare` (kernel and compiled lanes must agree):

* honest requests (indices = block mod N, bits from the items' values) are accepted;
* rejected: an index that is not its block mod N; an item changed so that it fails, one failure
  more than the claimed count; a request with one position missing; `same` flipped, so the kernel
  counts the complement; a malformed request.

The packed requests (`pool-sample-packed`, `pool-sample-packed-witness`) give the per-position
check's answer on every honest request and on a count one too low; unpacking their slots (as
`PoolSample.decodeDrawn` reads them) gives back the blocks, the indices and the items' numbers;
and they are rejected when an index is wrong, when an index is `≥ N` with a block that still
equals `N·q + j`, when one item fails more, when `same` is flipped, when a slot is too narrow for
its numbers, and when malformed.

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
from verifier.core.pool_rate import encode, pack, packed_sample_args, sample_args  # noqa: E402

KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"


def run(reqs):
    text = "".join(" ".join(r) + "\n" for r in reqs)
    out = subprocess.run([str(KERNEL), "--stdin", "--compare"], input=text, capture_output=True, text=True)
    if out.returncode == 3:
        raise SystemExit(f"[FAIL] lanes disagree:\n{out.stderr}")
    return [l == "true" for l in out.stdout.splitlines()]


def packed(N, same, n, S, mQ, mJ, T, part, d, blocks, qs, js, xs, ys):
    """A packed request with every field given, honest or not."""
    k, a, b, witness = part
    head = [N, int(same), n, S, mQ, mJ, T, k, a, b] + ([] if witness is None else list(witness)) + [d]
    name = "pool-sample-packed" if witness is None else "pool-sample-packed-witness"
    return [name, *map(str, head), *map(hex, [pack(blocks, S), pack(qs, S), pack(js, S), pack(xs, T), pack(ys, T)])]


def unpacks(r, blocks, N, pairs) -> bool:
    """`decodeDrawn` of the request is the positions the verifier checked."""
    nums = [int(x, 0) for x in r[1:]]
    N_, _, n, S, _, _, T = nums[:7]
    Bk, _, J, A, C = nums[-5:]
    slot = lambda w, i, x: (x >> (w * i)) % (1 << w)
    return all((slot(S, i, Bk), slot(S, i, J), slot(T, i, A), slot(T, i, C)) ==
               (blocks[i], blocks[i] % N, encode(pairs[i][0]), encode(pairs[i][1])) for i in range(n))


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

        # the packed form
        for wit in (None, (1, 2)):
            pt = (fails, 1, 2, wit)
            pr = packed_sample_args(blocks, N, pairs, False, pt, 2)
            add(pr, True, f"{case}: packed honest ({'witness' if wit else 'exact'})")
            if not unpacks(pr, blocks, N, pairs):
                raise SystemExit(f"[FAIL] {case}: the packed request does not store the checked positions")
            if fails > 0:
                add(packed_sample_args(blocks, N, pairs, False, (fails - 1, 1, 2, wit), 2), False,
                    f"{case}: packed, count one too low")
        pt = (fails, 1, 2, witness)
        nums = [int(x, 0) for x in packed_sample_args(blocks, N, pairs, False, pt, 2)[1:]]
        _, _, _, S, mQ, mJ, T = nums[:7]
        qs, js = [b // N for b in blocks], [b % N for b in blocks]
        xs, ys = [encode(x) for x, _ in pairs], [encode(y) for _, y in pairs]
        bad_js = list(js); bad_js[i] = (js[i] + 1) % N
        add(packed(N, False, n, S, mQ, mJ, T, pt, 2, blocks, qs, bad_js, xs, ys), False,
            f"{case}: packed, index is not block mod N")
        # j + N with q − 1: the block is still N·q + j, but the index is not below N
        bq, bj = list(qs), list(js); bq[i] -= 1; bj[i] += N
        mJ2 = (2 * N).bit_length()
        S2 = max(((N << mQ) + (1 << mJ2) - 1).bit_length(), mJ2 + 1)
        add(packed(N, False, n, S2, mQ, mJ2, T, pt, 2, blocks, bq, bj, xs, ys), False,
            f"{case}: packed, index ≥ N with a consistent block")
        if pairs[i][0] == pairs[i][1]:
            bx = list(xs); bx[i] = encode("bad")
            T2 = max(T, encode("bad").bit_length() + 1)
            add(packed(N, False, n, S, mQ, mJ, T2, pt, 2, blocks, qs, js, bx, ys), False,
                f"{case}: packed, one failure more than the claimed count")
        if (n - fails) > fails:
            add(packed(N, True, n, S, mQ, mJ, T, pt, 2, blocks, qs, js, xs, ys), False,
                f"{case}: packed, counted the complement")
        add(packed(N, False, n, S, mQ, mJ, T - 1, pt, 2, blocks, qs, js, xs, ys), False,
            f"{case}: packed, item slots without a guard bit")
        pr = packed_sample_args(blocks, N, pairs, False, pt, 2)
        add(pr[:-1], False, f"{case}: packed, malformed")
    got = run(reqs)
    failures = [f"{s}: expected {w}, got {g}" for s, w, g in zip(what, want, got) if w != g]
    if len(got) != len(reqs):
        failures.append(f"expected {len(reqs)} answers, got {len(got)}")
    for f in failures:
        print(f"[FAIL] {f}")
    if failures:
        return 1
    print(f"{len(reqs)}/{len(reqs)} pool-sample cases pass (per position and packed); kernel and compiled "
          "lanes agree; every packed request unpacks to the checked positions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
