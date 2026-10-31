# Assurance levels (v0.1)

Every method in `methods/` and every guarantee in `catalog/` carries exactly one level.
CI enforces the requirements below with `tests/regression/check_catalog.py` and the axiom audit.

| Level | Meaning | What you trust |
| --- | --- | --- |
| **verified** (gold standard) | A wrong result cannot be accepted. | The Lean kernel, the Lean statement of the specification, the listed assumptions. |
| **specified** | The intended result is defined formally, but the code that runs is not proved to compute it. | The above, plus the implementation. |
| **experimental** | No formal specification. The result is evidence, not a guarantee. | The implementation, the setup and the people who ran it. |

## verified

All six are required.

1. **Specification.** A Lean definition or statement says what the result means
   (for example, "population error ≤ p with probability ≥ 1 − δ").
2. **Correctness theorem.** A kernel-checked theorem says that every accepted result meets
   the specification, under assumptions listed in [`../assumptions/`](../assumptions/).
3. **The execution path is covered**, in one of two modes:
   - `verified-implementation`: the algorithm is a Lean definition and the kernel evaluates it
     (`decide +kernel`, `rfl`). Example: the quantized network is re-run by the kernel.
   - `verified-checker`: untrusted code computes the result and a witness, and a kernel-checked
     check accepts it. Example: Python finds the tightest binomial bound, and the kernel checks the integer
     inequality behind it. A bug in the untrusted code can cause a rejection, never a false
     acceptance.
   - **Decision procedures.** When the check is a `Bool`-valued Lean definition whose meaning is a
     kernel-checked theorem (for example `Checks.poolCheck` with `PoolRate.Claim.of_poolCheck`),
     the kernel evaluates the definition on each certificate (`ot_kernel`); that run is `verified`. The same
     definition can also run as compiled code (`ot verify --compiled`, `ot_check`), which is faster
     but trusts the Lean compiler: such a run is labelled separately and is never `verified`. No
     theorem depends on a compiled run. CI compares both lanes (`ot_kernel --compare`).
4. **Exact semantics.** The kernel checks integers, rationals or intervals. A proof over `ℝ` of an
   algorithm that runs in floating point is **specified**, not verified, unless the rounding
   error is bounded in Lean.
5. **Audit.** There is no `sorry`, and the only axioms are `propext`, `Classical.choice` and
   `Quot.sound`. This rules out `native_decide`, whose `Lean.ofReduceBool` trusts the compiler,
   inside any proof.
6. **Conformance.** Tests show that honest inputs are accepted and tampered inputs are rejected.

## specified

- Lean specification required, ideally with a correctness theorem for the abstract algorithm.
- The implementation must be named, together with the reason it is not covered (floating point,
  random initialization outside the theorem's hypotheses, unverified library).
- Output must carry the label `specified`.

## experimental

- Anything else: probes, evals, research code, heuristics.
- Output must carry the label `experimental`. It is never the only basis for a certificate.
- Everything under `research/` is experimental by definition.

## Composition

- A guarantee's level is **at most the lowest level** of the methods it uses.
- Assumptions are not levels. They are listed separately in every certificate and never hidden.
- A level is not permanent. If a referenced Lean declaration disappears or gains a `sorry`, CI
  fails until the manifest is fixed or demoted.

## Formal results versus methods

Theorems in `formal/` that are not tied to a running algorithm are tracked in the blueprint.
A `\leanok` proof there means no `sorry`. A theorem alone does not make any method `verified`.
