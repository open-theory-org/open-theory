# How OpenTheory fits together

What the system is made of, why it is systematic, what it can certify today and what remains.
The objects are defined in [../language.md](../language.md), the trust in [../trust.md](../trust.md),
the statistics in [../statistics.md](../statistics.md).

Running example: a bank's credit model and two sentences it wants a regulator to be able to check:

> *"The model approves every applicant within ±5% of Alice's income."* (white box: the model file)
>
> *"At most 3% of this month's 100,000 decisions fail their review."* (black box: logged decisions)

## 1. One picture

```
                   untrusted                              trusted, and why
  ┌──────────────────────────────────────┐   ┌────────────────────────────────────────────┐
  │ the world: model file, logged         │   │ formal/core (Lean): what a claim means and  │
  │ decisions, beacon round, labels       │   │ why a check implies it, proved once         │
  │            │                          │   │      ▲ claim types, Sound theorems          │
  │            ▼                          │   │      │                                      │
  │ methods/ (producers): build the       │   │ specs/ + catalog/: which claim, which       │
  │ certificate and its witnesses         │   │ method, which assumptions; CI checks every  │
  │            │                          │   │ link against Lean                           │
  │            ▼                          │   │      ▲                                      │
  │ certificate bundle (data only)  ──────┼──►│ verifier: ot verify → ot_kernel (the Lean   │
  │                                       │   │ kernel evaluates the check) → result line   │
  └──────────────────────────────────────┘   └────────────────────────────────────────────┘
```

A bug in a producer can make an honest certificate fail, never a false one pass. What the result
line asks you to trust is the Lean kernel, the statement of the claim type, and the listed
assumptions.

## 2. The parts

| Part | What it is | Written in | Checked by |
| --- | --- | --- | --- |
| **Language** | `Spec` (observable × domain × aggregate), `Sound`, `ClaimType`, the model interface (`HasDecision`, `HasScore`), the properties | `formal/core/{Properties,Scopes,Specs}` | the Lean kernel |
| **Models** | families built from primitives: exact ReLU networks (linear, ReLU), quantized MLPs (proved members of that family), tree ensembles | `formal/core/Models` | the Lean kernel |
| **Rules** | for each family and check, the theorem that an accepted check implies the claim | `formal/core/{Scopes,Specs}`, `Specs/ClaimTypes.lean` | the Lean kernel |
| **Checks** | the decision procedures the kernel runs per certificate, in core Lean only | `formal/core/Checks` | the Lean kernel (equal to their reference form, proved) |
| **Registries** | cards: models, properties, domains, claims; assumptions | `specs/` | `check_specs.py`, `check_spec_shapes.py` |
| **Catalog** | methods (how a claim is checked) and guarantees (what a certificate names), levels derived | `catalog/` | `check_catalog.py` |
| **Producers** | untrusted code that builds certificates and witnesses | `methods/` | conformance tests |
| **Verifier** | `ot verify` (orchestration, cryptographic attestations), `ot_kernel` (kernel lane), `ot_check` (compiled lane) | `verifier/`, `interfaces/` | conformance tests, both lanes compared |

`formal/core` is layered, each layer importing only earlier ones (CI: `check_layers.py`):

```
Checks (core Lean only) → Foundations → Models → Properties → Theory → Scopes → Specs
```

[core-map.md](core-map.md) marks each module as **claim** (a certificate rests on it) or **library**
(a formal result behind no claim yet).

## 3. Is it systematic, formal, built from the ground up and checkable?

| Requirement | Yes, because | Enforced by |
| --- | --- | --- |
| **Formal** | every object a certificate mentions is a Lean definition: the spec, the property, the model, the claim type, the guarantee `Sound`; a claim is a Lean proposition | the kernel; `check_lean_decls.py` (every name a card or manifest uses exists) |
| **Built from the ground up** | the claim types rest on measure theory, exact arithmetic and models built from primitives, in a fixed layer order; checks use core Lean only | `check_layers.py`; the axiom audit (only `propext`, `Classical.choice`, `Quot.sound`) |
| **One language for every claim** | every claim type is a term of one structure `ClaimType`, with the one guarantee `Sound`; claims combine by `Sound.and` | Lean typing |
| **Properties across families** | a property is stated once against the model interface; a family provides it by an instance; one card per spec, one claim type per family | `check_specs.py` (`needs` ⊆ `implements`) |
| **Cards say what Lean says** | each card's property, kind, domain, aggregate and model are read from the elaborated claim types | `check_spec_shapes.py` |
| **Levels are earned** | a method is `verified` exactly when the kernel checks a chain from its evidence to a claim type's `Sound`, with a conformance test | `check_catalog.py`, `test_catalog_levels.py` |
| **Nothing hidden** | every assumption says which Lean object it ties to the world (law, observable, domain, model), and a certificate must list them | `check_specs.py`, `ot verify` |
| **The two lanes agree** | the compiled check is proved equal to the kernel's, and tested on honest, tampered and random certificates | `runRobust_eq`, `runPoolSample_eq`, …; `ot_kernel --compare` |
| **O(1) to extend** | a model family, a property, a claim type or a method is one Lean term and one card or manifest; everything else is generated (`coverage.md`, the catalog tables, the core map) | the generators fail CI when stale |

**What is not systematic, and cannot be:**
- **A rule is a proof.** Each claim type's check and its `Sound` theorem are written once, by hand,
  for each family. The language makes the statement uniform and the check mechanical, but the
  proof is the work.
- **Semantic fidelity is read, not checked.** No machine can say that a Lean statement means what
  its card says in words. That is why a statement enters `formal/` only after a human reads it.
- **Assumptions are about the world**, outside any proof. The system makes them explicit.

**What is not systematic yet:**
- The model interface has two classes, so properties about internals, sequences or agents have no
  interface yet.
- The quantized MLP does not provide `HasDecision`: it breaks ties towards the first class, while
  the network decision needs a strict maximum.
- 61 of the 72 `Theory/` modules are library: formal results behind no claim.

## 4. What Lean lets us certify today

| Card | In words (running example) | Access | Model families | δ | Level |
| --- | --- | --- | --- | --- | --- |
| `robust-decision` | the decision is the same for every input in a box (Alice ± 5%) | white box | tree ensembles; ReLU networks (theorem, no method yet) | 0 | verified (trees) |
| `monotone-feature` | raising one feature (income) never lowers the score | white box | tree ensembles | 0 | verified |
| `heldout-error` | the error rate on the population is at most `p` | white box + IID held-out data | quantized MLPs | `δ` | verified |
| `occam-code-error`, `pacbayes-error` | the same, for a model trained on the sample | white box + training data | quantized MLPs | stated | verified |
| `pool-rate` | at most `p` of the committed decisions fail | black box (logged outputs) | any system | stated | verified |
| `judged-rate` | the same, failures graded by a judge and a small gold audit | black box + judge + gold labels | any system | stated | verified |
| `rate-gap`, `rate-ratio` | approval rates of two groups differ by at most `ε`, or their ratio is at least 0.8 | black box | any system | stated | verified |
| `mlp-exact` | the network outputs exactly `Y` on `x` | white box | ReLU networks | — | experimental (no soundness proof) |

The live versions, with every claim type, method, fast check and assumption, are generated in
[specs/coverage.md](../../specs/coverage.md) and [catalog/README.md](../../catalog/README.md).

## 5. Procedures, by access to the system

How much of the system a procedure sees decides which properties it can certify, and which
assumptions it needs:

| Access | What the producer has | What the kernel checks | Properties it reaches | Today |
| --- | --- | --- | --- | --- |
| **Black box** | logged inputs and outputs on a committed pool; a public beacon | the sample derived from the beacon, the outcomes from the committed bytes, the count and the tail | rates of any event of the outputs; gaps and ratios between groups | `pool-rate`, `rate-gap`, `rate-ratio` |
| **Black box + judgement** | the above, a committed AI judge, gold labels on a small prefix | the parts' counts and tails (the outcomes: verifier, for now) | failure rates against gold labels | `judged-rate` |
| **White box: the model** | the model file (weights, trees) | the model itself: re-evaluation, interval propagation, reachable leaves | decisions on regions, monotonicity, error on held-out data, generalization | `robust-decision`, `monotone-feature`, `heldout-error`, `occam`, `pacbayes` |
| **White box: internals** | activations, attention heads, circuits | a mechanistic claim (a circuit computes a function, an ablation changes little) | interpretability claims | library theorems only (`Theory/Function`, head ablation); `methods/whitebox/` is empty |
| **Runtime** | every action of a running system | a gate checks each action against a policy | an agent never takes a forbidden action | planned (agent policy gate) |

Black-box claims need no model file and no assumption about the data (design-based); white-box
claims need the model and its binding to the deployed one (A3), and for trees its translation
(A11). A white-box per-item check feeds a black-box rate: "robust on 99% of applicants" is
`robust-decision` per item, then `pool-rate` (planned as `robust-accuracy`).

## 6. The verifiers

| Component | Does | Trusted? |
| --- | --- | --- |
| `ot verify` (`verifier/core/`) | reads the bundle, checks digests, timestamps (RFC 3161), the drand beacon (BLS) and Merkle inclusions; translates tree models (A11); builds the request; runs the kernel; prints the result line | the cryptographic steps are assumptions (A5, A6, A12); everything else is cross-checked |
| `ot_kernel` | builds `check args = true` and has the Lean kernel evaluate it; `--show` prints what the request decodes to, `--compare` runs both lanes | the **verified** lane: the Lean kernel |
| `ot_check` | the same checks compiled; proved equal to the kernel's | labelled "compiled check, not verified" |
| `held-out` path | writes a Lean file from the claim template and the data, then `lean` checks it | the kernel; the template is fixed by the verifier |
| `audit_axioms.lean` | every OpenTheory declaration: no `sorry`, standard axioms only | CI |
| `interfaces/mcp` | lets a local agent find open blueprint targets and check proofs with the kernel | not a verifier of certificates |

Kernel times are in [../benchmarks.md](../benchmarks.md): 2 ms for a 100k-parameter MLP, 28 ms for a
1,000-item beacon sample, 0.16 s for 500 trees.

## 7. What remains

| Area | Next |
| --- | --- |
| **Speed** | packed kernel checks (trees first, then beacon samples and large Chernoff tails), aiming at sub-millisecond ([../PLAN.md](../PLAN.md)) |
| **Claim types for the bank** | calibration (the first quantity), AUC, quantiles, `robust-accuracy` (white box per item, then a rate) |
| **Open chains** | `judged-rate` outcomes in the kernel; a method for `robust-decision` on networks; a soundness proof for `mlp-exact`; the quantized MLP's decision |
| **Access levels** | internals (`methods/whitebox/`, an interface for activations), runtime (the agent gate) |
| **Trust** | your reading of the pending statements; a second, independent checker |
| **Product** | the end-to-end credit-model report on a public dataset; zero-knowledge or attestation to show results without the model |
