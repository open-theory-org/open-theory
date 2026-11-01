Verifying AI Models: a taxonomy of specifications.


# Introduction

AI safety needs guarantees about the behavior of AI systems: that a model is accurate on the
population it serves, that a decision does not flip under a small change of input, that an agent
never takes a forbidden action. Scalable oversight [@amodei2016concrete; @bowman2022measuring],
alignment and capability control all rest on such guarantees.

In the case of AI, empirical guarantees are not enough. A benchmark score can be gamed, an audit set
can be anticipated [@luck2026certified], and an evaluation report is only as good as the trust we
place in whoever ran it. We need guarantees that are formal, that anyone can verify independently,
and that scale to real models and real deployments.

Formal verification has shown that this is possible for parts of the problem
[@katz2017reluplex; @seshia2022toward; @dalrymple2024guaranteed]. The missing step is earlier: the
clarification of the claims themselves. A claim must be formalized before it can be verified.
Formalization is the prerequisite of verification.

OpenTheory is a framework for turning knowledge about AI systems into independently verifiable
guarantees. This document gives its taxonomy: a map of the claims that can be verified, and the way
each claim is built. It is the stepping stone for everything else: once properties and
specifications are fixed, we can say exactly which Lean theorem proves what, and build the catalog
of methods on top.


# Verification and Models

A verification claim has three parts: a **claim**, the **evidence** that supports it, and the
**assumptions** under which the evidence supports it. A **verifier** checks that the evidence
establishes the claim under the assumptions:

$$\underbrace{A}_{\text{assumptions}} \quad\Longrightarrow\quad \underbrace{P}_{\text{desired property}}.$$

Two questions must both be answered:

- **Mathematical correctness**: does the proof establish the formal statement? The Lean kernel
  answers this one.
- **Semantic fidelity**: does that statement accurately express the intended claim about the
  system? Only a careful reading of the statement answers this one, which is why every statement is
  read by a human before it enters `formal/`.

AI models belong to families. A ReLU network of any depth and width is one family; a gradient-boosted
tree ensemble is another; a deployed system seen only through its outputs is a third. A model is
built by composing primitives (linear layers, activations, attention, trees), so that a fact proved
once for each primitive holds for every model built from them.

Trained models have properties. They have a size, they generalize or not, they behave in a certain
way on given inputs, and their behavior has statistical regularities under given assumptions. A
**property of a model is anything that can be true of it**, written `P(M)`. Some are directly
relevant to safety (a decision is robust, a monitor fires), others are means to them (a Lipschitz
constant, a bound on the parameters). Several properties can hold at once, and the same property
can be asked of every model in a family.

The basic unit is therefore a property, formalized, about a model, inside a claim.


# Properties

Models have a considerable number of properties, but not all are equally relevant. We classify them
by their **core object**: what the property is about.

| Core object | What it is | Example properties |
| --- | --- | --- |
| The learned function | `f : X → Y`, the input–output map | correctness on an input, robustness on a region, monotonicity in a feature, fairness between inputs, equivalence of two models |
| The statistical predictor | `f` together with the distribution it serves | error rate, AUC, calibration, generalization from training data |
| The data | what trained and evaluated the model | held-out data was unseen, labels are correct, no contamination |
| The architecture | parameters and structure | size, Lipschitz bounds, quantization, the primitives it is built from |
| The internals | activations, heads, circuits | a circuit is faithful, ablating heads changes little |
| Inference | the deployed computation | the served model is the certified one (hardware, attestation), privacy of the prompt and of the weights |
| Behavior over multiple steps | an agent acting in a loop | it never takes a forbidden action, it respects a constraint |
| A changing environment | the world the system acts in | guarantees under bounded distribution shift |

A property is stated as a **yes/no test on one input**: "the model's scores rank class `c` first on
`x`", "the model's answer on `x` is correct", "the agent's action at state `x` is allowed". In Lean:

```lean
abbrev Property (M X : Type*) := M → X → Prop
```

A test on one input is the right unit because it combines. The same test, asked of every input in a
region or of most inputs of a population, gives every kind of claim below.


# Specifications

A specification says what is looked at, where, and what is asked of it. It has three fields.

**The observable.** A property (a yes/no test, as above), or a **quantity**: a value of the model
on one input in `[0, 1]`, such as a bounded loss or a score. Calibration and the Brier score need
quantities. A property's value is `1` where it holds and `0` elsewhere, so its mean over a
population is its rate. The input may be a tuple: a pair `(x, x')` for monotonicity and individual
fairness, a pair `(pos, neg)` for AUC, a whole trace for an agent.

**The domain.** Which inputs the specification is about:

| Domain | Meaning |
| --- | --- |
| Region `R` | every input of a set: a box around an applicant, a finite list of inputs |
| Committed pool | a finite pool of items fixed before any sample is drawn, each with weight `1/N` |
| Distribution `D` | the population the examples were drawn from, known only through an assumption (A1) |
| Pair | two of the above, compared with each other: two groups, two time windows, two versions |

A pool and a distribution are different claims with different assumptions, which is why the domain
names its population.

**The aggregate.** What is asked of the domain: the observable holds everywhere (`all`); its mean,
or rate, is at most or at least a bound (`meanLe`, `meanGe`); a quantile is at most a bound
(`quantileLe`); and on a pair, the two means differ by at most `ε` (`gapLe`) or have a ratio at
least `c` (`ratioGe`).

```lean
inductive Observable (M X)  | property (P : M → X → Prop) | quantity (Q : M → X → ℝ)
inductive Domain (X)        | region (R : Set X) | pool (N : ℕ) (item : Fin N → X)
                            | distribution (D : Measure X) | pair (d₁ d₂ : Domain X)
inductive Aggregate         | all | meanLe (a) | meanGe (a) | quantileLe (α t)
                            | gapLe (ε) | ratioGe (c)

structure Spec (M X) where
  observable : Observable M X
  domain     : Domain X
  aggregate  : Aggregate
```

Its **target**, `Spec.Target σ m`, is what it asks of the model `m`. Combinations without a
meaning, such as a mean over a region or a gap over a single domain, have the target `False`: no
certificate can establish them. Every known claim fits:

| Claim | Observable | Domain | Aggregate |
| --- | --- | --- | --- |
| error rate on production data | property: wrong | committed pool | rate ≤ `p` |
| held-out error | property: wrong | distribution | rate ≤ `p` |
| local robustness | property: predicts `c` | region (a ball) | all |
| monotonicity | property on `(x, x')`: `x ≤ x' ⇒ f(x) ≤ f(x')` | region | all |
| calibration, Brier score | quantity | committed pool | mean ≤ `m` |
| demographic parity | property: approved | pair of pools (two groups) | gap ≤ `ε` |
| disparate impact | property: approved | pair of pools | ratio ≥ `0.8` |
| AUC | property on `(pos, neg)`: ranked correctly | pairs from two pools | rate ≥ `q` |
| latency p99 | quantity | committed pool of runs | quantile ≤ `t` |

A **claim** is a specification with its numbers filled in, for one model: "this model predicts
class 0 on every input within 3 of `x₀`", "this model errs on at most 3% of the population, with
confidence 99.9%". A **claim type** is a specification with its numbers left as parameters,
together with the theorem that gives its guarantee; each card in `specs/claims/` is one claim type.
A **certificate** is the evidence that a verifier checks for one claim. Every object is defined
once in `docs/language.md`.

Every certificate gives the same guarantee, whatever its specification:

```lean
def Sound (P : Measure Ω) (accepts : Ω → Θ → Prop) (target : Θ → Prop) (δ : ℝ) : Prop :=
  P {ω | ∃ θ, accepts ω θ ∧ ¬ target θ} ≤ δ
```

In words: **over the randomness of how the evidence was collected, the probability that the check
accepts a claim that is false is at most `δ`**, even when the certifier chooses the claim (the
count, the bound, the box) after seeing the evidence. For a region there is no randomness and
`δ = 0`: an accepted claim is true. This one sentence is what a certificate means, and what a
regulator or an auditor can rely on.

A specification is checkable when a rule proves `Sound` for its combination of aggregate, domain,
observable and model family. Each rule is proved once, for every observable of its class; trees on
regions and gaps and ratios between pools are proved; the open ones, in the order the bank
milestone needs them, are means of quantities (calibration), then AUC (`specs/taxonomy.md`).


# Assurance

Not every guarantee is of the same kind. Each certificate states its **assurance type**:

| Assurance type | Meaning |
| --- | --- |
| Formal | A mathematical proposition has a valid machine-checked proof |
| Deterministic | A specified system property has been established for a stated scope |
| Statistical | A probabilistic guarantee follows under documented assumptions |
| Empirical | An observed result is supported by reproducible evaluation evidence |
| Cryptographic | A defined computation or relation is proven without exposing specified private information |
| Runtime | An enforcement mechanism has checked or enforced a specific operational constraint |

and its **assurance level**, which says how much of the chain is machine-checked
(`specs/protocols/assurance-levels.md`): `verified` when the Lean kernel checks the certificate
against a proved specification, `specified` when the specification is formal but the
implementation is not, `experimental` otherwise. A region claim checked by the kernel is formal,
deterministic and `verified`. A population claim is statistical, and `verified` only for the
sampling procedure its assumptions describe.

**Assumptions are never hidden.** Each one has an id (`specs/assumptions/`): the sample is IID
(A1), the held-out data was not used in training (A2), the certified model is the deployed one
(A3), the labels are correct (A4). Each scope brings its own, and a claim lists all of them.


# A Taxonomy of properties

Combining the core object, the property and the scope gives the map of claims. A cell is the
specification "this property, on this scope"; its status is what the repository can certify today.

| Core object | Property | Region | Population |
| --- | --- | --- | --- |
| Learned function | prediction constant around an input | theorem, kernel check (ReLU MLPs) | robust accuracy (planned) |
| Learned function | exact output on an input | kernel check, `experimental` (ReLU MLPs) | — |
| Learned function | decision constant on a box, monotonicity | `verified` (tree ensembles) | — |
| Learned function | fairness between inputs | planned | fairness rates `verified` (rate-gap, rate-ratio) |
| Statistical predictor | error rate | — | `verified` (quantized MLPs) |
| Statistical predictor | AUC, calibration | — | planned |
| Any system, black box | rate of an event on a committed pool | — | `verified` (pool-rate, judged-rate) |
| Architecture | Lipschitz bound, interval soundness | theorem for every ReLU MLP | — |
| Internals | head-ablation fidelity | theorem only | — |
| Behavior over steps | allowed actions | planned (agent gate) | violation rate (planned) |

This table is a summary. The authoritative version, `specs/coverage.md`, is generated from the
registries in `specs/` (one card per model, property, scope and claim) and the levels in
`catalog/`, and CI fails when it drifts from what is proved.


# Proofs

In Lean, a property holds when it follows from given quantities. For each certificate we can
evaluate the model directly, or compute a proof from it. Either is expensive if done again for
every claim.

The efficient design is to share assumptions and proofs across instances, compute only the
necessary model-specific statistics, and make the final certificate checks simple:

- **Proved once**: for each specification, the theorem that an accepting check gives the guarantee
  above. For a family of models, it is proved once per primitive and composed.
- **Computed per model**: the statistics the check needs (counts, bounds, packed weights), by
  untrusted code.
- **Checked per certificate**: a `Bool` decision procedure, run by the Lean kernel in about a
  millisecond for 100k parameters, or compiled (faster, but it trusts the compiler and is labelled
  accordingly).

Finding the most adequate quantities for each property, and the algorithms that compute and check
them quicker and cheaper, is an active area of research.


# References

All citations are keys of `blueprint/src/references.bib`. The literature map behind the taxonomy is
`research/literature/verifiable-traditional-ml.md`.
