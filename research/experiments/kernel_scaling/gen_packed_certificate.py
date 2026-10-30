#!/usr/bin/env python3
"""End-to-end packed error-count theorem for the 784-256-10 probe network.

Usage: gen_packed_certificate.py OUT_DIR [ROWS ...]

Same random network and rows as gen_packed.py (same seed). Emits, for each
ROWS, `packed_cert_<ROWS>.lean` proving

    errorCount arch (codeOfList _ (net.codes arch)) (packedObservations 20 784 rows) = e

through `errorCount_packed`, with every side condition discharged by
`decide +kernel`. Also emits `packed_cert_bad.lean` with a wrong count, which
must fail. The expected count comes from the Python mirror of the decoder.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "methods" / "statistical"))
from pacbayes_mlp_certificate import scores, argmax_first  # noqa: E402

ARCH = dict(inputs=784, hidden=256, classes=10, hidden_bias_scale=256, output_bias_scale=512)
B = 20


def pack(digits):
    v = 0
    for t in reversed(digits):
        v = (v << B) | t
    return v


def emit(out, name, rows1, rest, ones, rows, errs):
    a = ARCH
    r1 = ",\n  ".join(hex(r) for r in rows1)
    body = ",\n  ".join(f"({hex(x)}, {y})" for x, y in rows)
    (out / name).write_text(f"""import Models.QuantizedMLP.Packed

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10

namespace PackedProbe
open OpenTheory.QuantizedMLP OpenTheory.Kronecker

def arch : Arch := ⟨{a['inputs']}, {a['hidden']}, {a['classes']}, {a['hidden_bias_scale']}, {a['output_bias_scale']}⟩

def net : Packed := ⟨{B}, [
  {r1}],
  {rest}⟩

def ones : ℕ := {hex(ones)}

theorem net_valid : net.Valid arch ones where
  rows1_length := by decide +kernel
  rows1_lt := by decide +kernel
  rows1_mask := by decide +kernel
  ones_eq := by decide +kernel
  eight_le := by decide +kernel
  no_carry := by decide +kernel

theorem net_rest : net.rest.length = arch.hidden + arch.hidden * arch.classes + arch.classes := by
  decide +kernel

def rows : List (ℕ × ℕ) := [
  {body}]

theorem rows_ok : ∀ z ∈ rows, InputOK net.slotBits arch.inputs z.1 := by decide +kernel

/-- The error count of the decoded 203,530-parameter network on the decoded rows. -/
theorem batch_errors :
    errorCount arch (codeOfList _ (net.codes arch)) (packedObservations net.slotBits arch.inputs rows) =
      {errs} := by
  rw [errorCount_packed net_valid net_rest rows_ok]
  decide +kernel

end PackedProbe
""")


def main(out, counts):
    out = Path(out)
    rng = random.Random(20261024)
    d, h, c = ARCH["inputs"], ARCH["hidden"], ARCH["classes"]
    p = d * h + h + h * c + c
    codes = [rng.randrange(4) for _ in range(p)]
    model = dict(ARCH, codes=codes)
    data = []
    for _ in range(max(counts)):
        x = [rng.randrange(256) if rng.random() < 0.2 else 0 for _ in range(d)]
        data.append((x, rng.randrange(10)))
    rows1 = [pack(codes[j * d:(j + 1) * d]) for j in range(h)]
    rest = codes[d * h:]
    ones = pack([1] * d)
    for k in counts:
        chunk = data[:k]
        errs = sum(argmax_first(scores(model, x)) != y for x, y in chunk)
        rows = [(pack(list(reversed(x))), y) for x, y in chunk]
        emit(out, f"packed_cert_{k}.lean", rows1, rest, ones, rows, errs)
        if k == min(counts):
            emit(out, "packed_cert_bad.lean", rows1, rest, ones, rows, errs + 1)
        print(k, "rows,", errs, "errors")


if __name__ == "__main__":
    main(sys.argv[1], [int(v) for v in sys.argv[2:]] or [1, 20])
