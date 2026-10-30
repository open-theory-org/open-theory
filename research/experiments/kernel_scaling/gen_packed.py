#!/usr/bin/env python3
"""Packed-encoding probe: time kernel checking of an MNIST-sized 2-bit MLP.

Usage: gen_packed.py OUT_DIR

Same network and rows as gen_probe.py (same seed), same decoder
(`OpenTheory.QuantizedMLP`), same `decide +kernel` proof of the error count.
Only the literals change: weights are stored as base-4 digits of ~200 large
naturals and each image as the base-256 digits of one natural, decoded by the
kernel. `set_option profiler true` reports per-declaration elaboration and
kernel type-checking time.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "methods" / "statistical"))
from pacbayes_mlp_certificate import scores, argmax_first  # noqa: E402

ARCH = dict(inputs=784, hidden=256, classes=10, hidden_bias_scale=256, output_bias_scale=512)
CHUNK = 1000


def pack(digits, base):
    x = 0
    for d in reversed(digits):
        x = x * base + d
    return x


def header(chunks, p):
    a = ARCH
    lits = ",\n  ".join(str(c) for c in chunks)
    return f"""import Models.QuantizedMLP.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 50

namespace MnistProbe
open OpenTheory.QuantizedMLP

/-- The first `k` base-`b` digits of `x`, least significant first. -/
def digits (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => x % b :: digits b k (x / b)

def arch : Arch := ⟨{a['inputs']}, {a['hidden']}, {a['classes']}, {a['hidden_bias_scale']}, {a['output_bias_scale']}⟩

def networkChunks : List ℕ := [
  {lits}]

def networkCodes : List ℕ := (networkChunks.flatMap (digits 4 {CHUNK})).take {p}

theorem networkCodes_length : networkCodes.length = arch.parameterCount := by decide +kernel

def network : Code arch.parameterCount 4 := codeOfList _ networkCodes

def image (x : ℕ) : List ℤ := (digits 256 {a['inputs']} x).map Int.ofNat
"""


def main(out):
    out = Path(out)
    rng = random.Random(20261024)
    d, h, c = ARCH["inputs"], ARCH["hidden"], ARCH["classes"]
    p = d * h + h + h * c + c
    codes = [rng.randrange(4) for _ in range(p)]
    model = dict(ARCH, codes=codes)
    rows = []
    for _ in range(20):
        x = [rng.randrange(256) if rng.random() < 0.2 else 0 for _ in range(d)]
        rows.append((x, rng.randrange(10)))
    padded = codes + [0] * (-len(codes) % CHUNK)
    chunks = [pack(padded[i:i + CHUNK], 4) for i in range(0, len(padded), CHUNK)]
    head = header(chunks, p)
    (out / "packed_net.lean").write_text(head + "\nend MnistProbe\n")
    for k in (1, 5, 20):
        chunk = rows[:k]
        errs = sum(argmax_first(scores(model, x)) != y for x, y in chunk)
        body = ",\n  ".join(f"(image {pack(x, 256)}, {y})" for x, y in chunk)
        (out / f"packed_rows_{k}.lean").write_text(head + f"""
def batch : List Observation := [
  {body}]

theorem batch_errors : errorCount arch network batch = {errs} := by
  rw [network, errorCount_codeOfList _ _ networkCodes_length]
  decide +kernel

end MnistProbe
""")
    print("params", p, "chunks", len(chunks))


if __name__ == "__main__":
    main(sys.argv[1])
