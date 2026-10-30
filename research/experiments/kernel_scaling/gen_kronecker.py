#!/usr/bin/env python3
"""Kronecker-substitution micro-probe: all 256 hidden dot products of the
784-256-10 probe network (same seed as gen_packed.py) for one image, checked
by `decide +kernel` with one big-integer product per hidden unit."""
import random, sys
from pathlib import Path
out = Path(sys.argv[1])
rng = random.Random(20261024)
d, h, c = 784, 256, 10
p = d * h + h + h * c + c
codes = [rng.randrange(4) for _ in range(p)]
x = [rng.randrange(256) if rng.random() < 0.2 else 0 for _ in range(d)]
B = 20                                   # 3 * 255 * 784 < 2^20: no carries between slots
def pack(ds):                            # ds[0] is the least significant slot
    v = 0
    for t in reversed(ds):
        v = (v << B) | t
    return v
W = [pack(codes[j * d:(j + 1) * d]) for j in range(h)]
X = pack(list(reversed(x)))              # reversed, so slot d-1 of W*X is the dot product
expected = [sum(codes[j * d + i] * x[i] for i in range(d)) for j in range(h)]
assert all((w * X >> (B * (d - 1))) % (1 << B) == e for w, e in zip(W, expected))
lits = ",\n  ".join(hex(w) for w in W)
(out / "kronecker_256.lean").write_text(f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 50

def Ws : List Nat := [
  {lits}]

def X : Nat := {hex(X)}

def dotK (w : Nat) : Nat := (w * X / 2 ^ {B * (d - 1)}) % 2 ^ {B}

theorem hidden_dots : Ws.map dotK = {expected} := by decide +kernel
""")
print("ok", len(W))
