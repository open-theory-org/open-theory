# The OpenTheory language

Every object the repository uses to state, prove and check a guarantee, defined once. The
motivation and the taxonomy are in [specs.md](specs.md); this page is the reference.

Running example: a bank's credit model (a gradient-boosted tree ensemble) and the sentence

> *"This model approves every applicant within ±5% of Alice's income, other features fixed."*

## 1. The objects

They are listed bottom up: each one is built from the ones above it.

| Object | What it is | In Lean | Written in | Running example |
| --- | --- | --- | --- | --- |
| **Model family** | a set of models, all of one Lean type `M` | the type `M` | `specs/models/` (field `type`) | tree ensembles, `Checks.Tree.Ensemble` |
| **Observable** | a test of a model on **one** input: a property (yes/no) or a quantity (a value in `[0, 1]`) | `Observable M X`: `.property (P : M → X → Prop)` or `.quantity (Q : M → X → ℝ)` | `specs/properties/` (field `kind`) | `decision`: "the model approves `x`" |
| **Domain** | which inputs: a region, a committed pool, a distribution, or a pair of these | `Domain X`: `.region`, `.pool`, `.distribution`, `.pair` | `specs/domains/` | the region "income within ±5% of Alice's" |
| **Aggregate** | what is asked of the domain: everywhere, a mean bound, a quantile, a gap or a ratio | `Aggregate`: `.all`, `.meanLe a`, `.meanGe a`, `.quantileLe α t`, `.gapLe ε`, `.ratioGe c` | in the claim card | `all` |
| **Spec** | observable × domain × aggregate; its **target** is a statement about one model | `Spec M X`; `s.Target σ m : Prop` | inside a `Sound` theorem | "`decision` holds on every `x` of the box" |
| **Claim type** | a spec with free parameters `θ`, an acceptance check, and the `Sound` theorem tying them | a theorem `Sound P accepts (fun θ => (spec θ).Target σ m) δ` | `specs/claims/` (one card per type) | `tree-robust`, with `θ = (box, c)` and `treeRobust_sound` |
| **Claim** | a claim type with `θ`, the model and `δ` filled in: one sentence, true or false | `(spec θ).Target σ m` for concrete values | the certificate | the sentence above, `δ = 0` |
| **Certificate** | the evidence for one claim, which the verifier checks | its fields are the arguments of `accepts ω θ` | a bundle (`specs/certificates/`) | the scaled trees, the box and `c = approve` |
| **Assumption** | a condition under which the guarantee holds, with an id | a hypothesis of the `Sound` theorem, or outside Lean (protocol, world) | `specs/assumptions/` | A3: the certified model is the deployed one; A11: the integer ensemble is the LightGBM model, scaled |
| **Method** | how certificates are produced and checked: producer, check, correctness theorems | `lean.check` (what the kernel evaluates), `lean.correctness` | `catalog/methods/` | `tree-ensemble-check` |
| **Guarantee** | what a certificate names: one claim type, the methods it uses, a level, every assumption | none: a name for the combination | `catalog/guarantees/` | "certified robust decision of a tree ensemble" |
| **Level** | how much of the chain the kernel checks: `verified`, `specified`, `experimental` | derived from the links (section 3) | `specs/protocols/assurance-levels.md` | `verified`: a kernel check, its correctness theorems and a conformance test |

Changing one field gives another claim type:

| Change | Claim type |
| --- | --- |
| domain: committed pool of this month's applicants; aggregate: `meanLe p`; observable: "wrongly declined" | `pool-rate` |
| domain: pair of pools (two groups); aggregate: `gapLe ε`; observable: "approved" | `rate-gap` (demographic parity) |
| observable on pairs `(x, x')`: "raising income does not lower the score" | `tree-monotone` |

## 2. The one guarantee

Every claim type gives the same guarantee:

```lean
def Sound (P : Measure Ω) (accepts : Ω → Θ → Prop) (target : Θ → Prop) (δ : ℝ) : Prop :=
  P {ω | ∃ θ, accepts ω θ ∧ ¬ target θ} ≤ ENNReal.ofReal δ
```

Over the randomness `ω` of how the evidence was collected, the check accepts some false claim with
probability at most `δ`. The parameters `θ` may be chosen after seeing the evidence. A region
has no randomness: `δ = 0`, and an accepted claim is true (`sound_exact_iff`).

## 3. What proves what

A certificate is believed through three links, each proved or checked once:

```
the kernel runs the check on the certificate            method:    lean.check
      ⇓  correctness theorems (proved once)            method:    lean.correctness
the acceptance condition `accepts ω θ` holds
      ⇓  the Sound theorem (proved once per claim type) claim card: sound
the claim is true, except with probability δ
```

In the running example: the kernel evaluates `Checks.Tree.robustCertK` on the trees, the box
and one bound per tree; `robustCertK_eq` and `robustCert_sound` show that acceptance means every
input of the box is approved; `treeRobust_sound` states it as `Sound` with `δ = 0`. The table
"what proves what" in [catalog/README.md](../catalog/README.md) gives this chain for every claim
type.

## 4. What is checked mechanically, and what is not

| Checked by CI | Script |
| --- | --- |
| every proof, with no `sorry` and only the standard axioms | `lake build`, `audit_axioms.lean` |
| every Lean name in a card, a manifest or the blueprint exists | `check_lean_decls.py`, `check_specs.py`, `check_catalog.py` |
| each claim card's observable kind, domain, aggregate and model are those of its `Sound` theorems | `check_spec_shapes.py` |
| an aggregate is used only on a domain where it has a meaning; a claim type lists its domain's assumptions and its methods' | `check_specs.py` |
| a method's level is the one its links support; a guarantee's level is that of its weakest method | `check_catalog.py` |
| a certificate is accepted by the kernel lane and the compiled lane alike | `fast_check.py`, `pool_check_lanes.py` |
| every citation resolves | `check_references.py` |

**Not checkable by a machine, so read by a human:** whether a Lean statement means what its card
says in words (semantic fidelity); the assumptions that are not hypotheses of a Lean theorem
(A3–A10: binding, beacon, timestamps, labels, group membership), together with the protocols that
discharge them; and whether a claim type is the right one to ask for. This is why a statement
enters `formal/` only after a human reads it.

## 5. Words used in one sense only

| Word | Means | Does not mean |
| --- | --- | --- |
| property | a yes/no test on **one** input (`M → X → Prop`) | the whole statement about the model, which is a spec's target |
| spec | observable × domain × aggregate | a specification document |
| claim type | a card in `specs/claims/`: a spec with parameters and its `Sound` theorem | one claim |
| claim | one sentence: a claim type with its numbers and its model | a template |
| method | how a claim type is checked (`catalog/`) | what is claimed (`specs/`) |
| guarantee | the name a certificate gives: claim type + methods + level | a theorem |
