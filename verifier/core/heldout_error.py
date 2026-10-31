"""Claim type `heldout-error` v0.1 for `model_type = "quantized-mlp"`.

Writes the Lean file the kernel checks. The theorem statement is fixed by the template
`OpenTheory.HeldOut.Claim` (formal/core/Specs/HeldOut.lean). The bundle supplies
integers only. The per-batch error counts below are computed here only to split the kernel's
work; if they are wrong, the kernel rejects.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from .engine import Reject, require

BATCH = 20
THEOREM = "OTVerify.certificate"
ARCH_KEYS = ("inputs", "hidden", "classes", "hidden_bias_scale", "output_bias_scale")


@dataclass
class Task:
    lean: str
    theorem: str
    words: str
    guarantee: str
    checked: list[str]
    trusted: list[str]
    does_not_cover: list[str]
    explain: callable = field(repr=False, default=lambda out: "")
    # Optional decision procedure run as compiled Lean (`ot_check` arguments), its Lean name with
    # arguments, the once-proved theorem giving its meaning, and why it would be false.
    fast: list | None = None
    fast_call: str = ""
    fast_meaning: str = ""
    fast_explain: callable = field(repr=False, default=lambda: "")


def parameter_count(m):
    d, h, c = m["inputs"], m["hidden"], m["classes"]
    return d * h + h + h * c + c


def scores(m, ws, x):
    """Mirror of `QuantizedMLP.scoresOfWeights` (zips truncate like `List.zipWith`)."""
    d, h, c = m["inputs"], m["hidden"], m["classes"]
    rows = lambda k, r, v: [v[i * k:(i + 1) * k] for i in range(r)]
    dot = lambda a, b: sum(p * q for p, q in zip(a, b))
    rest = ws[d * h:]
    out = rest[h:]
    hidden = [max(0, dot(r, x) + m["hidden_bias_scale"] * b) for r, b in zip(rows(d, h, ws), rest[:h])]
    return [dot(r, hidden) + m["output_bias_scale"] * b for r, b in zip(rows(h, c, out), out[h * c:][:c])]


def argmax_first(s):
    best = (s[0] if s else 0, 0)
    for i, v in enumerate(s):
        if best[0] < v:
            best = (v, i)
    return best[1]


def parse_fraction(obj, where):
    num, den = require(obj, "num", int, where), require(obj, "den", int, where)
    if den <= 0 or not 0 <= num <= den:
        raise Reject(f"{where}: need 0 ≤ num ≤ den and den > 0")
    return num, den


def parse_model(m):
    if m.get("model_type") != "quantized-mlp":
        raise Reject("model.model_type must be 'quantized-mlp'")
    for k in ARCH_KEYS:
        require(m, k, int, "model")
    if min(m["inputs"], m["hidden"], m["classes"]) <= 0:
        raise Reject("model: inputs, hidden and classes must be positive")
    codes = require(m, "codes", list, "model")
    if len(codes) != parameter_count(m):
        raise Reject(f"model: {len(codes)} codes, architecture needs {parameter_count(m)}")
    if any(type(v) is not int or not 0 <= v < 4 for v in codes):
        raise Reject("model: codes must be integers in [0, 4)")
    return m, codes


def parse_rows(data, inputs):
    rows = require(data, "rows", list, "heldout")
    if not rows:
        raise Reject("heldout: no rows")
    for i, r in enumerate(rows):
        if not isinstance(r, list) or len(r) != inputs + 1 or any(type(v) is not int for v in r) or r[-1] < 0:
            raise Reject(f"heldout.rows[{i}]: need {inputs} integer inputs and a non-negative integer label")
    return rows


def lean_source(m, codes, rows, k, num, den, d):
    ws = [v - 2 for v in codes]
    n = len(rows)
    arch = ", ".join(str(m[key]) for key in ARCH_KEYS)
    parts = [f"""import Specs.HeldOut

set_option maxRecDepth 100000

namespace OTVerify
open OpenTheory.QuantizedMLP OpenTheory.HeldOut OpenTheory.BinomialTail

def arch : Arch := ⟨{arch}⟩

def codes : List ℕ := {codes}

theorem codes_length : codes.length = arch.parameterCount := by decide +kernel
"""]
    names, counts = [], []
    for i in range(0, n, BATCH):
        name = f"batch{i // BATCH:03d}"
        batch = rows[i:i + BATCH]
        c = sum(argmax_first(scores(m, ws, r[:-1])) != r[-1] for r in batch)
        names.append(name)
        counts.append(c)
        body = ",\n  ".join(f"({r[:-1]}, {r[-1]})" for r in batch)
        parts.append(f"""
def {name} : List Observation := [
  {body}]

theorem {name}_errors : errorCountOfWeights arch (weightsOfList codes) {name} = {c} := by decide +kernel
""")
    parts.append(f"""
def rows : List Observation := {" ++ ".join(names)}

theorem rows_length : rows.length = {n} := by decide +kernel

theorem count_le : errorCountOfWeights arch (weightsOfList codes) rows ≤ {k} := by
  simp only [rows, errorCountOfWeights_append, {", ".join(f"{x}_errors" for x in names)}] <;> decide

theorem tail : {d} * tailNumerator rows.length {k} {num} {den} ≤ {den} ^ rows.length := by
  rw [rows_length]; decide +kernel

/-- The `heldout-error` claim, stated by the verifier from the certificate's parameters. -/
theorem certificate :
    Claim (classificationLoss arch) (codeOfList arch.parameterCount codes)
      (QuantizedMLP.sampleOf rows) {k} (({num} : ℕ) / ({den} : ℕ) : ℝ) (1 / ({d} : ℕ)) :=
  QuantizedMLP.claim arch codes codes_length rows count_le (by decide) (by decide) (by decide) tail

end OTVerify

#print axioms {THEOREM}
""")
    return "".join(parts), names, counts


def explain(out, source, counts, k, num, den, n):
    """Name the first failing theorem, using the line numbers Lean reports."""
    import re
    starts = [(i + 1, m.group(1)) for i, line in enumerate(source.splitlines())
              if (m := re.match(r"theorem (\w+)", line))]
    for m in re.finditer(r"Check\.lean:(\d+):\d+: error", out):
        line = int(m.group(1))
        name = next((nm for ln, nm in reversed(starts) if ln <= line), "")
        if name == "count_le":
            return f"the kernel re-ran the network: {sum(counts)} errors on the held-out rows, more than the claimed {k}"
        if name == "tail":
            return (f"the data do not support the bound {num}/{den}: P(Bin({n}, {num}/{den}) ≤ {k}) exceeds δ "
                    "(the integer tail inequality is false)")
        if name.endswith("_errors"):
            return f"{name}: a recomputed batch count disagrees with the kernel (verifier bug: please report)"
        return f"{name or 'file'}: " + out[m.end():].strip().splitlines()[0][:200]
    return "unknown Lean error"


def handle(bundle: Path, cert: dict, load_file) -> Task:
    claim = cert["claim"]
    if require(claim, "version", str, "claim") != "0.1":
        raise Reject("claim.version must be '0.1'")
    k = require(claim, "errors", int, "claim")
    num, den = parse_fraction(require(claim, "bound", dict, "claim"), "claim.bound")
    dn, d = parse_fraction(require(claim, "delta", dict, "claim"), "claim.delta")
    if dn != 1 or d < 2:
        raise Reject("claim.delta must be 1/d with d ≥ 2 in v0.1")
    if k < 0:
        raise Reject("claim.errors must be non-negative")

    subject = require(cert, "subject", dict, "certificate")
    model, model_sha = load_file(bundle, require(subject, "model", dict, "subject"), "subject.model")
    m, codes = parse_model(model)
    evidence = require(cert, "evidence", dict, "certificate")
    data, data_sha = load_file(bundle, require(evidence, "heldout", dict, "evidence"), "evidence.heldout")
    rows = parse_rows(data, m["inputs"])
    n = len(rows)
    declared_n = evidence["heldout"].get("n")
    if declared_n is not None and declared_n != n:
        raise Reject(f"evidence.heldout.n = {declared_n} but the file has {n} rows")

    lean, names, counts = lean_source(m, codes, rows, k, num, den, d)
    shape = f"{m['inputs']}-{m['hidden']}-{m['classes']}"
    return Task(
        lean=lean,
        theorem=THEOREM,
        guarantee="heldout-accuracy-quantized-classifier",
        words=(f"With probability ≥ {1 - 1 / d:.0%} over the draw of the {n} held-out examples, the "
               f"population error of model sha256:{model_sha[:16]}… ({shape} quantized MLP, "
               f"{len(codes)} parameters) is ≤ {num / den:.2%}. Observed: ≤ {k} errors on held-out data "
               f"sha256:{data_sha[:16]}…"),
        checked=[
            "model and held-out sha256 digests (verifier)",
            f"network re-run on all {n} rows: ≤ {k} errors (Lean kernel)",
            f"integer tail inequality {d}·tailNumerator({n}, {k}, {num}, {den}) ≤ {den}^{n} (Lean kernel)",
            "theorem type is the template OpenTheory.HeldOut.Claim with the certificate's parameters (written by the verifier, proved by the kernel)",
        ],
        trusted=[
            "statement of OpenTheory.HeldOut.Claim and the OpenTheory library it imports",
            "this verifier's JSON → Lean data translation (verifier/core/heldout_error.py)",
        ],
        does_not_cover=[
            "data from a different distribution (distribution shift)",
            "any model other than this exact integer network (A3 binds it to a deployment)",
            "label errors in the held-out set (A4)",
        ],
        explain=lambda out: explain(out, lean, counts, k, num, den, n),
    )


HANDLERS = {"heldout-error": handle}
