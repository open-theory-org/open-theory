#!/usr/bin/env python3
"""The `pool` and `pool-witness` checks (`formal/core/Checks/PoolRate.lean`) and their packed forms
`pool-packed`, `pool-packed-witness` (bits one per slot, `Checks/PoolSample.lean`): both lanes, one answer.

Sends random requests, honest and broken (stray bits above `n`, too small a halving depth `l`,
understated counts, bounds one step too tight; for the packed forms, a bit in a slot past `n` and
a slot holding 2), to `ot_kernel --compare --stdin`, which evaluates
each in the Lean kernel and in the compiled lane (`ot_check`) and reports any disagreement. Each
answer must also match an independent Python reading of the check. Standard library only;
requires `lake build ot_kernel`.
"""
from __future__ import annotations

import random
import subprocess
import sys
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"
sys.path.insert(0, str(ROOT / "methods" / "statistical"))
from binomial_bound import tightest_bound  # noqa: E402


def levels(n: int) -> int:
    return max(0, ((n + 63) // 64 - 1).bit_length())


def tail(n: int, k: int, a: int, b: int) -> int:
    return sum(comb(n, i) * a ** i * (b - a) ** max(n - i, 0) for i in range(k + 1))


def common(x, n, l, k, a, b, d) -> bool:
    return x >> n == 0 and n <= 64 << l and bin(x).count("1") <= k and a <= b and b > 0 and d > 0


def main() -> int:
    rng = random.Random(2026)
    lines, want = [], []
    for _ in range(250):
        n = rng.choice([1, 2, 63, 64, 65, 129, 500, 2000])
        ones = rng.randint(0, min(n, 60))
        x = sum(1 << i for i in rng.sample(range(n), ones))
        if rng.random() < 0.08:
            x |= 1 << (n + rng.randint(0, 3))
        l = levels(n) - (1 if levels(n) > 0 and rng.random() < 0.08 else 0)
        k = max(0, ones + rng.choice([-1, 0, 0, 0, 2]))
        b, d = rng.choice([100, 100000]), rng.choice([2, 1000, 10 ** 6])
        a = max(0, min(b, tightest_bound(n, min(k, n), b, d) + rng.choice([-1, 0, 0, 1])))
        lines.append(f"pool {hex(x)} {n} {l} {k} {a} {b} {d}")
        want.append(common(x, n, l, k, a, b, d) and d * tail(n, k, a, b) <= b ** n)
        u, v = rng.randint(1, 1 << 20), 1 << 20
        lines.append(f"pool-witness {hex(x)} {n} {l} {k} {a} {b} {u} {v} {d}")
        want.append(common(x, n, l, k, a, b, d) and d * (b * v - a * v + a * u) ** n * v ** k <= (b * v) ** n * u ** k)
        # packed: the same bits one per slot; a stray bit past n lands in slot n
        T = (2 * n + 1).bit_length() + 1
        X = sum(1 << (T * i) for i in range(n + 4) if x >> i & 1)
        two = rng.random() < 0.08 and x & ((1 << n) - 1)
        if two:
            X += 1 << (T * (x & -x).bit_length() - T)        # the lowest set bit's slot becomes 2
        okp = x >> n == 0 and not two and bin(x).count("1") <= k and a <= b and b > 0 and d > 0
        lines.append(f"pool-packed {T} {n} {k} {a} {b} {d} {hex(X)}")
        want.append(okp and d * tail(n, k, a, b) <= b ** n)
        lines.append(f"pool-packed-witness {T} {n} {k} {a} {b} {u} {v} {d} {hex(X)}")
        want.append(okp and d * (b * v - a * v + a * u) ** n * v ** k <= (b * v) ** n * u ** k)
    lines += ["pool 0x1 3 0 1", "pool-witness 0xZZ 1 0 0 1 2 1 1 2"]
    want += ["error", "error"]
    res = subprocess.run([str(KERNEL), "--compare", "--stdin"], input="\n".join(lines) + "\n",
                         capture_output=True, text=True)
    got = res.stdout.splitlines()
    bad = [(ln, g, w) for ln, g, w in zip(lines, got, want)
           if (g.startswith("error") if w == "error" else g == str(w).lower()) is False]
    if len(got) != len(lines) or bad or res.returncode != 0:
        for ln, g, w in bad[:10]:
            print(f"[FAIL] {ln[:80]}…: kernel {g}, expected {w}")
        print(res.stderr.strip()[-500:])
        print(f"\n{len(lines) - len(bad)}/{len(lines)} pool-check cases pass (exit {res.returncode})")
        return 1
    print(f"{len(lines)}/{len(lines)} pool-check cases pass ({sum(w is True for w in want)} accepted); "
          "kernel and compiled lanes agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
