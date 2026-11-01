# The OpenTheory language

Every object the repository uses to state, prove and check a guarantee, defined once: what it
is, its Lean form, where it is written, and what checks it. The motivation and the taxonomy are in
[specs.md](specs.md); this page is the reference.

Running example: a bank's credit model (a gradient-boosted tree ensemble) and the sentence

> *"This model approves every applicant within ±5% of Alice's income, other features fixed."*

## 1. The objects

Listed bottom up: each is built from the ones above it. Every object that is a Lean term has a
card in `specs/` (or a manifest in `catalog/`) that names it, and CI checks that the two agree.

| Object | What it is | In Lean | Written in | Running example |
| --- | --- | --- | --- | --- |
| **Model family** | a set of models, all of one Lean type `M` | the type `M` | `specs/models/` (field `type`) | tree ensembles, `Checks.Tree.Ensemble` |
| **Property** | a yes/no test of a model on **one** input | a named definition `P : Property M X` (`M → X → Prop`) | `specs/properties/` (fields `kind`, `lean`) | `decision`: `Ensemble.Decides c`, "the model's decision on `x` is `c`" |
| **Quantity** | a value of a model on one input, in `[0, 1]` (a loss, a score) | `Q : Quantity M X` (`M → X → ℝ`) | `specs/properties/` (`kind = "quantity"`) | — (calibration will be the first) |
| **Observable** | a property or a quantity; a property's value is `1` where it holds, so its mean is its rate | `Observable M X`: `.property P`, `.quantity Q` | — | `.property (Ensemble.Decides c)` |
| **Domain** | which inputs: a region, a committed pool, a distribution, or a pair of these | `Domain X`: `.region`, `.pool`, `.distribution`, `.pair` | `specs/domains/` | the region "income within ±5% of Alice's" |
| **Aggregate** | what is asked of the domain | `Aggregate`: `.all`, `.meanLe a`, `.meanGe a`, `.quantileLe α t`, `.gapLe ε`, `.ratioGe c` | in the claim card | `all` |
| **Spec** | observable × domain × aggregate; its **target** is a statement about one model | `Spec M X`; `s.Target m : Prop` | inside a claim type | "the decision is `c` on every `x` of the box" |
| **Claim type** | a spec with its numbers left as parameters, the evidence and its law, what the check accepts, and the theorem that gives the guarantee | a term of `ClaimType M X` (`Specs/ClaimTypes.lean`) | `specs/claims/` (one card; field `claim_types`) | `ClaimTypes.treeRobust e`, parameters `(box, c, bounds)` |
| **Claim** | a claim type with its parameter: one sentence, true or false | `T.Claim θ` = `(T.spec θ).Target (T.model θ)` | the certificate | the sentence above, `δ = 0` |
| **Certificate** | the evidence for one claim, which the verifier checks | the arguments of `T.accepts ω θ` | a request or a bundle (`specs/certificates/`) | the scaled trees, the box, `c = approve`, one bound per tree |
| **Report** | several claims over one draw of evidence | `Sound.and`, `Sound.comap`: `δ` adds | — (planned: the credit report) | robustness for Alice + monotonicity in income |
| **Assumption** | why one Lean object of a claim type is the real one | not a Lean term: it bridges `law`, `observable`, `domain` or `model` to the world | `specs/assumptions/` (`**Bridges:**`) | A3: `model` is the deployed one; A11: the integer ensemble is the LightGBM model |
| **Method** | how certificates are produced and checked: producer, kernel check, correctness theorems | `lean.check` (what the kernel evaluates), `lean.correctness` | `catalog/methods/` (`establishes`, `feeds`) | `tree-ensemble-check` |
| **Guarantee** | what a certificate names: one claim type, the methods it uses, a level, every assumption | none: a name for the combination | `catalog/guarantees/` | — |
| **Level** | how much of the chain the kernel checks: `verified`, `specified`, `experimental` | derived from the links (section 4) | `specs/protocols/assurance-levels.md` | `verified` |

Changing one field gives another claim type:

| Change | Claim type |
| --- | --- |
| domain: committed pool of this month's applicants; aggregate: `meanLe p`; property: "wrongly declined" | `pool-rate` |
| domain: pair of pools (two groups); aggregate: `gapLe ε`; property: "approved" | `rate-gap` (demographic parity) |
| property on pairs `(x, x')`: "raising income does not lower the score" | `tree-monotone` |
| observable: a quantity (the predicted probability's squared error); aggregate: `meanLe m` | calibration (next) |

## 2. The claim type, and the one guarantee

```lean
structure ClaimType (M X) where
  Param    : Type                 -- what a certificate fills in, possibly after seeing the evidence
  Evidence : Type                 -- the randomness of how the evidence is collected
  law      : Measure Evidence
  accepts  : Evidence → Param → Prop
  spec     : Param → Spec M X
  model    : Param → M
  δ        : ℝ
  sound    : Sound law accepts (fun θ => (spec θ).Target (model θ)) δ

def Sound (P : Measure Ω) (accepts : Ω → Θ → Prop) (target : Θ → Prop) (δ : ℝ) : Prop :=
  P {ω | ∃ θ, accepts ω θ ∧ ¬ target θ} ≤ ENNReal.ofReal δ
```

Over the randomness `ω` of how the evidence was collected, the check accepts some false claim with
probability at most `δ`. The parameters `θ` may be chosen after seeing the evidence. A region
has no randomness: `δ = 0`, and an accepted claim is true (`sound_exact_iff`).

| Claim type | Evidence | δ |
| --- | --- | --- |
| `robustRegion`, `treeRobust`, `treeMonotone` | none | `0` |
| `heldOut`, `occam`, `pacBayes` | an IID sample | stated per claim type |
| `poolRate`, `judgedRate`, `rateGap`, `rateRatio` | a public beacon seed | stated per claim type |

**Claims combine.** Two checks on the same evidence accept a pair with a false claim with
probability at most `δ₁ + δ₂` (`Sound.and`, a union bound: no independence needed), and evidence
computed from a larger draw keeps its guarantee (`Sound.comap`). A report is a list of claims over
one draw; its `δ` is the sum of theirs.

## 3. Assumptions bridge Lean to the world

A proof is about the objects in Lean. An assumption says that one of them is the real one:

| Bridges | The Lean object | Assumptions |
| --- | --- | --- |
| `law` | the law of the evidence | A1 (IID), A2 (model fixed before the sample), A5 (uniform seed), A6 (seed after the commitment), A7 (all attempts counted) |
| `observable` | what the property tests | A4 (labels), A9 (gold labels) |
| `domain` | the population | A8 (the pool is the traffic), A10 (each pool is its group) |
| `model` | the model the claim is about | A3 (the deployed model), A11 (the LightGBM translation) |

Nothing else is assumed: a claim type's certificate lists its assumptions, and each one is one of
these four bridges.

## 4. What proves what

A certificate is believed through three links, each proved or checked once:

```
the kernel runs the check on the certificate              method:     lean.check
      ⇓  correctness theorems (proved once)              method:     lean.correctness
the acceptance `T.accepts ω θ` holds
      ⇓  T.sound (proved once per claim type)            claim card: claim_types
the claim T.Claim θ is true, except with probability T.δ
```

In the running example: the kernel evaluates `Checks.Tree.robustCertK` on the trees, the box
and one bound per tree, which is `ClaimTypes.treeRobust`'s acceptance; its `sound` field is
`treeRobust_sound` (from `robustCertK_eq` and `robustCert_sound`), with `δ = 0`. The table "what
proves what" in [catalog/README.md](../catalog/README.md) gives the chain for every claim type, and
[specs/coverage.md](../specs/coverage.md) maps them by model, property and domain.

A method's level is derived from these links, never only declared: `verified` exactly when it has
a mode, `lean.spec`, `lean.correctness` and a conformance test, and establishes claim types (or
feeds a method that does).

## 5. Why it is systematic

Each kind of object is written once and named everywhere else:

| To add | You write | Everything else |
| --- | --- | --- |
| a model family | its Lean type, a model card | reuses every property and claim type stated for any `M` |
| a property | one named definition, a property card | combines with every domain and aggregate already proved |
| a claim type | one `ClaimType` term (its check and `Sound` proof), a claim card | composes with every other claim (`Sound.and`), appears in the coverage and the catalog |
| a method | a producer, a manifest, a conformance test | gets its level derived, its row in "what proves what" |

The cost of an addition does not grow with what exists: the language (observable × domain ×
aggregate, one guarantee) is fixed, and every new piece is checked against it by the scripts below.

## 6. What is checked mechanically, and what is not

| Checked by CI | Script |
| --- | --- |
| every proof, with no `sorry` and only the standard axioms | `lake build`, `audit_axioms.lean` |
| every Lean name in a card, a manifest or the blueprint exists | `check_lean_decls.py`, `check_specs.py`, `check_catalog.py` |
| each claim card's named property, observable kind, domain, aggregate and model are those of its `ClaimType` terms | `check_spec_shapes.py` |
| an aggregate is used only on a domain where it has a meaning; a claim type lists its domain's assumptions and its methods' | `check_specs.py` |
| every assumption says which Lean object it bridges | `check_specs.py` |
| a method's level is the one its links support; a guarantee's level is that of its weakest method | `check_catalog.py` |
| a certificate is accepted by the kernel lane and the compiled lane alike; accepted claims hold on the original model | `fast_check.py`, `pool_check_lanes.py`, `tree_check.py` |
| every citation resolves | `check_references.py` |

**Not checkable by a machine, so read by a human:** whether a Lean statement means what its card
says in words (semantic fidelity); the assumptions, and the protocols that discharge them; and
whether a claim type is the right one to ask for. This is why a statement enters `formal/` only
after a human reads it.

## 7. Words used in one sense only

| Word | Means | Does not mean |
| --- | --- | --- |
| property | a yes/no test on **one** input (`M → X → Prop`), named in Lean | the whole statement about the model, which is a spec's target |
| observable | a property or a quantity | — |
| spec | observable × domain × aggregate | a specification document |
| claim type | a `ClaimType` term, and its card in `specs/claims/` | one claim |
| claim | one sentence: a claim type with its parameter | a template |
| assumption | a bridge from one Lean object (law, observable, domain, model) to the world | a hypothesis hidden in a proof |
| method | how a claim type is checked (`catalog/`) | what is claimed (`specs/`) |
| guarantee | the name a certificate gives: claim type + methods + level | a theorem |
