# OpenTheory plan

Revised 2026-10-27, after the hollow modules were deleted. It covers the open/closed strategy,
white-box certification, and what to build in which order.

## 1. Position

**OpenTheory is the open part.** It holds the definitions, the theorems, the claim templates,
the certificate format and a verifier anyone can run. With those, a third party can check a
claim about an AI system without trusting us or paying us. **Structure and Soul are the closed
part.** They hold the models, data, decision engines and the infrastructure that produces evidence
cheaply and at scale.

Public by necessity: what a claim means (its Lean statement and assumptions), why it follows (the
kernel-checked proof), and how to check it (format, verifier, conformance tests). Everything else
is private by choice.

Research question: *how can we derive independently checkable behavioural guarantees about
learned systems from incomplete information about them?*

## 2. The idea that makes this buildable now

The repo already contains the key theorem. `BinomialTail.count_testSet_bound` holds for **any**
measurable per-example event `E` and **any** data distribution. If `k` of `n` IID examples fall
outside `E` and `P(Bin(n,p) ≤ k) ≤ δ`, then with confidence `1 − δ` the population rate outside
`E` is at most `p`.

`E` does not have to be "the prediction is correct". It can be any property we can check on one
example, including properties that need the weights:

- the prediction cannot change under any perturbation of size `ε` (checked by bound propagation);
- the circuit we identified gives the same answer as the full model (checked by intervention);
- the probe or monitor fires correctly;
- the model refuses, or passes the tests, or stays within the policy.

So every white-box measurement that is a per-example yes/no becomes a **population guarantee
with stated confidence, under stated assumptions**. White-box access adds two things black-box
evaluation cannot give: per-example properties that hold **for all inputs in a region**, and
**global** properties read directly from the weights.

### The ladder of claim strength

| Level | Form | Example | How it is established |
| --- | --- | --- | --- |
| L0 evidence | "we measured X" | probe accuracy 95% on our set | experiment; not a certificate |
| L1 statistical | "with confidence 1−δ, rate ≥ 1−p in the population" | circuit agrees with model on ≥ 90% of prompts | per-example check + binomial theorem |
| L2 local universal | "for this input, for **all** x' in the region, P holds" | no ±1 pixel change flips this digit | bound propagation, checked in Lean |
| L3 global | "for **all** inputs, P holds" | removing head h moves logits by ≤ δ; output ignores feature j | inequality computed from the weights, checked in Lean |
| L1 ∘ L2 | "with confidence 1−δ, ≥ 1−p of the population is certified robust" | certified robust accuracy | L2 per example, then the binomial bound |

Interpretability results usually sit at L0. The plan is to move them to L1, and where the model is
small enough, to L2 and L3.

## 3. Certificates we can build now

"Kernel" means the Lean kernel recomputes everything, which is possible for small quantized
models. "Harness" means a reference evaluation harness computes the per-example bits, which are
committed by hash. That works for any model, including LLMs; the trust then rests on the harness
and the commitment.

| # | Certificate | Level | Method | Lean status | Scale |
| --- | --- | --- | --- | --- | --- |
| C1 | Held-out accuracy | L1 | Clopper–Pearson on error count | **done** (`examples/certified_accuracy`) | kernel: small; harness: any |
| C2 | Local robustness of one prediction | L2 | integer interval bound propagation (IBP) on the quantized MLP | soundness lemma to write; checking by `decide +kernel` | kernel |
| C3 | **Certified robust accuracy in the population** | L1∘L2 | C2 as the event `E` in the binomial theorem | C1 + C2 | kernel |
| C4 | Bounded influence of a protected feature | L2/L3 | zero weights give exact independence; otherwise IBP over the feature's range | C2 machinery | kernel |
| C5 | Global Lipschitz / margin radius | L3 | product of layer norms; spectral norm via a rational positive-semidefinite (PSD) witness | MLP and residual Lipschitz lemmas exist (`Torch`, `DeepResidualScaling`) | kernel for small nets |
| C6 | Component-ablation bound | L3 | `AttentionAblation`: removing heads moves outputs by ≤ Σ‖proj‖·B_V | **theorems exist**; need numeric instantiation | small transformer |
| C7 | Circuit faithfulness / interchange-intervention accuracy | L1 | activation patching per prompt, then binomial bound | template only | harness: GPT-2, Pythia, Gemma |
| C8 | Monitor with certified detection and false-alarm rates | L1 | probe on activations, scored on committed held-out sets, then binomial bound | template only | harness: any open-weight LLM |
| C9 | Concept erasure (linear guardedness) | L3 | after LEACE-style projection, no linear readout beats a constant predictor | theorem to formalize; per-model check is exact linear algebra | any, on one layer |
| C10 | Behavioural rates (refusal, pass@1 on verifiable tasks) | L1 | Inspect AI harness, then binomial bound | template only | any |
| C11 | Agent policy compliance | L2 over traces | decidable policy; Lean proves the reference monitor sound | to write | any agent |
| C12 | Private versions of C1/C3/C7/C11 | — | zkVM (SP1 / RISC Zero) proves the count without revealing weights | Lean side unchanged | small models first |

**What none of these prove.** They say nothing about distribution shift beyond the stated
distribution, nor that a metric captures "the mechanism". A certified circuit-faithfulness rate is
a certified *rate*, defined by the intervention protocol. None of them is a claim of general
safety. Each certificate lists its assumptions and trusted components explicitly.

**Sampling integrity.** Every L1 claim rests on "the evaluation examples are IID and not cherry-picked".
For generated distributions (IOI prompts, red-team templates), commit the model digest and the
generator code first. Then draw the seeds from a **public randomness beacon** (drand) published
after the commitment. For fixed datasets, commit the held-out hash to a transparency log (Sigstore
Rekor or SCITT) before training. The verifier checks the timestamps.

## 4. Flagships, in order

1. **Certified accuracy (C1).** Done mathematically; it needs the certificate format and verifier.
2. **Certified robust accuracy, fully kernel-checked (C2 + C3) on the digits network.** The
   claim: *"With 95% confidence, at least X% of digits from this distribution are classified
   correctly and cannot be flipped by any ±ε change to the pixels."* It needs no trust in us,
   in floating point, or in a solver: an untrusted program finds the bounds, and Lean checks
   them. This is the strongest white-box demo available and, as far as I know, uncommon in the
   literature.
3. **Certified mechanistic claim on an open LLM (C7 + C8).** Run the IOI circuit on GPT-2 small,
   a well-known and reproducible result. Then add a safety probe, such as a harmful-request or
   refusal-direction monitor, on Gemma-2-2B or Llama-3.2-1B, with certified detection and false-alarm
   rates. This is harness-attested, scales to real models, and links interpretability to alignment.

## 5. Repository structure

Layout: [architecture/repository.md](architecture/repository.md). In one line each:

- `specs/` defines the claims;
- `formal/` proves them;
- `methods/` produces evidence (untrusted);
- `verifier/` checks it;
- `interfaces/` exposes it;
- `catalog/` labels every method;
- `research/` and `examples/` hold experiments and demonstrations;
- `tests/` holds the conformance, integration, adversarial and regression suites.

**Assurance levels are the differentiator.** Every method is **verified**, **specified** or
**experimental** ([specs/protocols/assurance-levels.md](../specs/protocols/assurance-levels.md)).

- **verified** requires a Lean specification, a kernel-checked correctness theorem, exact semantics and a
  conformance test that rejects forgeries. The mode is either `verified-implementation`, where the kernel runs the
  algorithm, or `verified-checker`, where untrusted code finds the answer and the kernel checks it.
- `tests/regression/check_catalog.py` enforces this.
- Today 5 methods are verified, 1 is specified and 1 is experimental. Every new certificate type (C2–C12) should land as verified,
  or be labelled honestly as lower.

| Open | Closed |
| --- | --- |
| claim templates, theorems, verifier, conformance tests | fast bound-propagation provers and other optimized evidence generation |
| reference harness (correct, not fast) | circuit and feature discovery tooling at scale, if it becomes a real edge |
| the certificate format and its trust model | model weights, training data, Structure decision engine, Soul preference models |
| published research (plateau paper, theorems) | production telemetry, integrations, signing keys |

The rule: a closed prover may produce the evidence, but checking it must never need closed code.

## 6. Roadmap

**Revision 2026-10-31: first user and new priority.** The first user is a bank (for example
Barclays) that wants to check the reliability and robustness of production models and show the
result to regulators, auditors and counterparties. The milestone below comes first. Phases 3
(white-box LLM certificates) and 4 (global white-box bounds) are paused until it ships. The rungs
phases A–G (sampling, label audit, agent gate, …) continue and feed it. Landscape and sources:
`research/literature/verifiable-traditional-ml.md`.

### Milestone: certified credit-model report

For one production-style credit model (gradient-boosted trees, for example LightGBM on a public
credit dataset), a report in which every line is a certificate a third party re-checks with
`ot verify` / `ot_kernel`, with its level, assumptions and sources.

| Report line | Claim | How | Builds on |
| --- | --- | --- | --- |
| Performance on production data | error rate; AUC and calibration (new templates) | binomial bounds on committed, beacon-sampled production rows (commit the model first, then sample [@luck2026certified]) | `heldout-error`, rungs phase A |
| Stability | the same claims per time window | one certificate per window | the above |
| Local robustness | the decision is constant on a box around an applicant | exact for tree ensembles (polynomial ℓ∞ for large-spread ensembles [@calzavara2025boosted]); intervals for logistic regression and MLPs | `Scopes/OnRegion` |
| Monotonicity | the score never decreases in chosen features (income, …) | per-tree check, a sufficient condition for additive ensembles [@devos2021versatile] | new property |
| Fairness | approval-rate gap between groups, with confidence | one rate claim per group | `RateClaim`, rungs phase B (labels) |
| Binding and privacy | the certified model is the deployed one, without revealing it | model hash first; zero-knowledge or TEE later, integrated not built [@zhang2020zkdt; @waiwitlikhit2024zkaudit] | `specs/evidence/` |

Primitives to add: **tree ensembles** (exact semantics with rational thresholds), **logistic
regression**, **preprocessing** (scaling, binning, one-hot). Every check lives in
`formal/core/Checks/` (core Lean only) with its soundness theorem proved once in the library.

The report maps each line to what the regulator asks: independent validation (SS1/23 principle 4
[@pra2023ss1]) and accuracy and robustness (EU AI Act Article 15 [@euaiact2024]).

Order:

1. Tree-ensemble primitive: exact semantics, then its Lean statements for review (section 7).
   Done 2026-11-01 (`Checks/Tree`, `Models/Tree`, `Scopes/TreeRegion`, `Specs/Tree`).
2. Monotonicity and local robustness checks for tree ensembles, in both lanes. Done 2026-11-01
   (`tree-ensemble-check`, verified; LightGBM producer). Kernel time: robustness on a small box
   about 4 ms for 10 trees and 0.17 s for 500; global monotonicity 20 ms for 10 trees and 1.5 s
   for 500, at about 10–15 µs per visited node. Sub-millisecond needs data parallelism in big
   integers (as for the MLP check), not yet attempted.
3. AUC, calibration and fairness templates on top of `RateClaim`.
4. End-to-end example on a public credit dataset, and the report format.
5. The zero-knowledge or TEE path for showing results without the model.

**Verification lanes** (decided 2026-10-31). A check proved sound once is run per certificate by
the Lean kernel (`ot_kernel`, about 1–2 ms for 100k parameters; label `verified`) or by compiled
code (`ot_check`, faster; trusts the Lean compiler, so labelled separately, never `verified`).
Built: one registry for both lanes, differential testing in CI (`ot_kernel --compare`), kernel
re-check on demand. Planned: a second, independent checker that must agree; if a user requires
it, a checker compiled by a verified compiler, as `cake_lpr` does for SAT proofs
[@tan2021cakelpr].

**Sources.** Every method cites its sources in `blueprint/src/references.bib`, from manifests
(`references = [{ key, relation }]`), Lean docstrings and Markdown (`[@key]`) and the blueprint
(`\cite`); `tests/regression/check_references.py` fails on unknown keys.

**Deferred.** The soundness proof of the packed MLP check `mlp-exact` (the check stays,
`experimental`); attention and transformer primitives; further speed work.

### Earlier phases (2026-10-27)


**Phase 0 (week 0–1): housekeeping.**
Commit the rework on a branch. Add CI (`lake build`, axiom audit, `check_lean_decls.py`,
`tests/regression/statement_gate.py --fail`, `check_catalog.py` on new files). Decide on IP before pushing (section 8).

**Phase 1 (weeks 1–4): Certificate v0.1 (C1).**
- `formal/core/Specs/HeldOut.lean`: the claim as a fixed template. The verifier rejects any
  certificate whose theorem type differs from it, so a prover cannot prove an easier statement.
- `specs/certificates/schema.json`: subject digests, template id and parameters, evidence commitments,
  attestation method, assumptions from a fixed vocabulary, toolchain pins, validity scope.
- `verifier/core/` (+ `interfaces/cli`): rebuilds the Lean file from the bundle, runs the kernel and the axiom
  check, and checks digests and commitment timestamps.
- `tests/conformance/`: the five demo scenarios (done: `certified_accuracy.sh`) (honest, lie about the count, overclaim, tamper with
  data, tamper with the model).

Done when a stranger can verify a certificate offline and every tampering case fails.

**Status 2026-10-28:**

- Done:
  - the `HeldOut` template;
  - the certificate schema;
  - `ot verify` and `ot certify`;
  - the Python SDK;
  - conformance (1 accept, 14 rejects).
- Remaining:
  - pinning to a tagged release (only a warning today);
  - Sigstore signatures and transparency-log timestamps;
  - a clean-machine test by a third party.

**Phase 2 (weeks 3–8): white-box v0.2, certified robust accuracy (C2, C3, C4).**
- Lean: interval semantics for `QuantizedMLP.scoresOfWeights` over integer input boxes, with a
  soundness theorem: every input in the box gets scores inside the computed intervals.
  Certification is a decidable check that the true class's lower bound beats every other class's
  upper bound.
- Python: an untrusted bound finder. It starts with plain IBP; tighter linear-relaxation bounds
  (the CROWN family) can come later, provided they emit a witness Lean can check.
- Template `RobustAccuracy`: binomial bound on the event "correct and certified".
- C4 on the same network: the "pixel block j has bounded influence" certificate.

Done when `examples/robust_accuracy` produces a certificate the kernel accepts and the conformance
tests include a tampered witness.

**Phase 3 (weeks 5–11): white-box LLM certificates (C7, C8, C10).**
- `methods/whitebox/` and `methods/evaluations/`: deterministic activation patching and probing on TransformerLens/nnsight with
  pinned versions, seeded from a drand beacon round, emitting per-example bits plus commitments.
- Generic template `RateClaim`: "for the committed procedure and distribution, the event rate is
  ≥ 1−p with confidence 1−δ". It is the C1 theorem with `E` abstract.
- Demos: IOI faithfulness on GPT-2 small; a safety monitor on a 1–2B open model with certified
  detection rate (on a committed red-team set) and false-alarm rate (on committed benign traffic);
  refusal and pass@1 rates through Inspect AI.

Done when a third party can re-run the harness and reproduce the bits exactly, and the verifier
accepts the certificates.

**Phase 4 (weeks 8–14): global white-box bounds (C5, C6, C9).**
- Rational PSD witnesses for spectral norms, giving a certified Lipschitz constant and a robustness
  radius from the margin for small MLPs.
- Numeric instantiation of `AttentionAblation` on a small trained transformer: "removing heads S
  changes any output by at most δ for inputs with norm ≤ R".
- Formalize linear guardedness for concept erasure: once class-conditional means are equal, every
  linear predictor's covariance with the concept is zero. Then check it per model.

**Phase 5 (weeks 10–16): private verification and the Structure bridge (C11, C12).**
- zkVM program for the error count / certified count of the quantized MLP. The certificate
  combines the receipt with the unchanged Lean proof. It must state the remaining gap: the zkVM
  program equals the Lean decoder, ensured first by differential testing.
- Agent policy monitor with a Lean soundness proof, then a first Structure workflow: authorise an
  action only if the causal-effect interval clears zero and the policy holds.

**Ongoing research (publish).**
- Submit the plateau / singular learning theory paper.
- Conformal coverage in Lean, for calibrated monitors and thresholds.
- *Certified mechanistic claims*: interchange-intervention accuracy with confidence, a statistical
  version of causal abstraction.
- *White-box structure gives tighter bounds*: a small circuit or low effective dimension should
  shrink PAC-Bayes and compression bounds. This connects the plateau results (effective dimension)
  to certificates.
- Guarantees under bounded distribution shift.
- Port the four `research/hypotheses/unported_lean/` modules; reopen the five deleted targets as honest open problems.

Deprioritised until a customer pays for verification: economics, trading, tokens, escrow,
"universal" atlases.

## 7. Rules

- No method without a level. `verified` is earned in Lean, never declared.
- A module enters `formal/` only after a human reads its statements.
- No "optimal", "master", "universal" or "guarantee" in a name unless the statement says exactly
  that; conditional results name the condition.
- A weakened research target stays open.
- Every certificate type documents its threat model, trusted components and non-claims.
- Do not build cryptography; integrate existing proving systems and transparency logs.

## 8. Decisions needed

1. **IP.** `origin/main` is public and still has the deleted fake-ZK code in its history. The
   strongest work (plateau chain, certificate pipeline, Kronecker trick, paper) is untracked, so
   it is not yet public. Decide what to publish, patent or keep before the next push.
2. **Flagship 2 vs 3 first.** Robust accuracy (Phase 2) is fully kernel-checked and the most
   defensible. LLM certificates (Phase 3) are more visible and closer to alignment work. The two
   can run in parallel if there are two people.
3. **First external user.** Decided 2026-10-31: a bank checking its production models (see the
   milestone in section 6). Phase 3 remains the pitch to safety teams; Phase 5 to Structure
   customers.
4. **Verification lanes.** Decided 2026-10-31: `verified` means checked by the Lean kernel; a
   compiled check is labelled separately (section 6).
