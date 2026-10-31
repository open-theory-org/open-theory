#!/usr/bin/env python3
"""Conformance of the fast checks (`formal/core/Checks/`): both lanes, one answer.

Runs `ot_kernel --compare`, which evaluates every check in the Lean kernel and in the compiled
lane (`Entry.run`, what `ot_check` calls) and reports any disagreement. Cases:

* honest certificates must be accepted;
* tampered certificates (a wrong output, a changed weight, a changed input, each verified here
  to make a false claim) must be rejected;
* random corruptions of honest certificates must give the same answer in both lanes (the
  differential test of the compiled lane against the kernel), and may be accepted only if they
  leave the claim unchanged: no change at all, or a looser bound parameter (a digit bound `wb`,
  `a0`, `a`, or more gather rounds `lg`). Any other accepted corruption fails the test as a
  possible soundness bug;
* malformed requests must be usage errors.

Requires `lake build ot_kernel`.
"""
from __future__ import annotations

import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "methods" / "neural"))
from mlp_exact_certificate import certificate, random_network, request, tampered  # noqa: E402

KERNEL = ROOT / ".lake" / "build" / "bin" / "ot_kernel"
# shapes include a deeper net and an expanding layer (8 → 40, rows padded to spacing n + 1)
SHAPES = [[4, 3, 2], [16, 8, 4], [64, 16, 10], [32, 32, 32, 4], [8, 40, 3]]


def bound_params(args: list[int]) -> set[int]:
    """Positions of the parameters that only bound the claim: `wb`, `a0`, and each layer's `a`
    and `lg` (the short certificate is `s c wb D a0 U Y`, then `n a E lg PW B` per layer)."""
    return {2, 4} | {i for i in range(7, len(args)) if (i - 7) % 6 in (1, 3)}


def harmless(honest: list[int], bad: list[int]) -> bool:
    changed = [i for i in range(len(honest)) if honest[i] != bad[i]]
    return all(i in bound_params(honest) and bad[i] > honest[i] for i in changed)


def corrupt(args: list[int], rng: random.Random) -> list[int]:
    out = list(args)
    i = rng.randrange(len(out))
    op = rng.randrange(4)
    if op == 0:
        out[i] ^= 1 << rng.randrange(max(1, out[i].bit_length()))
    elif op == 1:
        out[i] += rng.choice([-1, 1]) if out[i] > 0 else 1
    elif op == 2:
        out[i] = 0
    else:
        j = rng.randrange(len(out))
        out[i], out[j] = out[j], out[i]
    return out


def main() -> int:
    if not KERNEL.exists():
        print(f"[FAIL] {KERNEL.relative_to(ROOT)} missing: run `lake build ot_kernel`")
        return 1
    cases: list[tuple[str, str, str]] = []  # (label, request, expected: true|false|any|error)
    # `any`: either answer, but `true` only for a harmless corruption (`false-only` otherwise)
    for dims in SHAPES:
        for seed in range(2):
            rng = random.Random(seed)
            layers, x = random_network(dims, 8, rng)
            honest = certificate(layers, x, 8)
            tag = f"{'-'.join(map(str, dims))} seed {seed}"
            cases.append((f"honest {tag}", request(honest), "true"))
            for kind, t in zip(["output", "weight", "input"], tampered(layers, x, 8, rng)):
                cases.append((f"tampered {kind} {tag}", request(t), "false"))
            for k in range(6):
                bad = corrupt(honest, rng)
                cases.append((f"corrupted #{k} {tag}", request(bad), "any" if harmless(honest, bad) else "false-only"))
    cases.append(("too few arguments", "mlp-exact 1 2 3", "error"))
    cases.append(("unknown check", "no-such-check 1", "error"))
    cases.append(("bad number", "mlp-exact 0xZZ", "error"))

    proc = subprocess.run([str(KERNEL), "--compare", "--stdin"], input="\n".join(c[1] for c in cases) + "\n",
                          capture_output=True, text=True, timeout=600)
    answers = proc.stdout.splitlines()
    failures = []
    if len(answers) != len(cases):
        failures.append(f"expected {len(cases)} answers, got {len(answers)}")
    for (label, _, expected), got in zip(cases, answers):
        ok = (expected == "any" and got in ("true", "false")) or (expected == "error" and got.startswith("error")) \
            or (expected == "false-only" and (got == "false" or got.startswith("error"))) or got == expected
        print(f"[{'ok' if ok else 'FAIL'}] {label}: expected {expected}, got {got}")
        if not ok:
            failures.append(label)
    disagreements = [l for l in proc.stderr.splitlines() if l.startswith("DISAGREE")]
    for d in disagreements:
        print(f"[FAIL] {d}")
    if proc.returncode not in (0,) or disagreements:
        failures.append(f"ot_kernel exit code {proc.returncode}, {len(disagreements)} lane disagreements")
    passed = len(cases) - len([f for f in failures if not f.startswith(("expected", "ot_kernel"))])
    print(f"\n{passed}/{len(cases)} fast-check cases pass; kernel and compiled lanes "
          f"{'agree' if not disagreements else 'DISAGREE'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
