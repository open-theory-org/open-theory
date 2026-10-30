#!/usr/bin/env python3
"""Generate Lean files that time kernel checking of an MNIST-sized 2-bit MLP.

Usage: gen_probe.py OUT_DIR

Emits, for a fixed random 784-256-10 network (same decoder and the same
`decide +kernel` proof shape as methods/statistical/pacbayes_mlp_certificate.py):
  net_only.lean      network literal + length check (no rows)
  rows_<k>.lean      network + one batch of k rows + error-count theorem
Kernel cost depends on the number of integer operations, not on the values,
so random weights and MNIST-range random pixels are representative.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "methods" / "statistical"))
from pacbayes_mlp_certificate import scores, argmax_first  # noqa: E402

ARCH = dict(inputs=784, hidden=256, classes=10, hidden_bias_scale=256, output_bias_scale=512)


def header(model):
    a = ARCH
    return f"""import Models.QuantizedMLP.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MnistProbe
open OpenTheory.QuantizedMLP

def arch : Arch := ⟨{a['inputs']}, {a['hidden']}, {a['classes']}, {a['hidden_bias_scale']}, {a['output_bias_scale']}⟩

def networkCodes : List ℕ := {model['codes']}

theorem networkCodes_length : networkCodes.length = arch.parameterCount := by decide +kernel

def network : Code arch.parameterCount 4 := codeOfList _ networkCodes
"""


def main(out):
    out = Path(out)
    rng = random.Random(20261024)
    d, h, c = ARCH["inputs"], ARCH["hidden"], ARCH["classes"]
    p = d * h + h + h * c + c
    model = dict(ARCH, codes=[rng.randrange(4) for _ in range(p)])
    rows = []
    for _ in range(20):
        x = [rng.randrange(256) if rng.random() < 0.2 else 0 for _ in range(d)]
        rows.append((x, rng.randrange(10)))
    (out / "net_only.lean").write_text(header(model) + "\nend MnistProbe\n")
    for k in (1, 5, 20):
        chunk = rows[:k]
        errs = sum(argmax_first(scores(model, x)) != y for x, y in chunk)
        body = ",\n  ".join(f"({x}, {y})" for x, y in chunk)
        (out / f"rows_{k}.lean").write_text(header(model) + f"""
def batch : List Observation := [
  {body}]

theorem batch_errors : errorCount arch network batch = {errs} := by
  rw [network, errorCount_codeOfList _ _ networkCodes_length]
  decide +kernel

end MnistProbe
""")
    print("params", p)


if __name__ == "__main__":
    main(sys.argv[1])
