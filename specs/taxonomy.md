# The spec language: extension of `docs/specs.md` (v0.1, approved 2026-10-31)

`docs/specs.md` defines the language: a **property** is a yes/no test of a model on one input, a
**scope** says where it must hold (`region R` or `population p`), a **spec** is the pair, and every
certificate gives one guarantee, `Sound`: over the randomness of how the evidence was collected,
the probability that the check accepts a false claim is at most `δ`, even when the claim's numbers
are chosen after seeing the evidence. This proposal keeps all of it and adds what the bank milestone
needs and the two scopes cannot express.

## 1. What is kept

`Property`, `Spec`, `Spec.Target`, `Sound`, claim, certificate, the core-object classification,
assurance types and levels, the registry cards and the generated `specs/coverage.md`. Every
existing template stays an instance, with the same guarantee.

## 2. What is added, and why

| Addition | Why it is needed | Backward compatible |
| --- | --- | --- |
| **The input may be a tuple** (a pair `(x, x')`, a pair `(pos, neg)`, a trace) | monotonicity, individual fairness and AUC compare two inputs; agent claims test whole traces | yes: `X` is any type, so this is a convention, not a new type |
| **Scope = domain + aggregate** | the current scope fixes the aggregate (∀ for regions, failure rate ≤ p for populations). Lower bounds, gaps and ratios between two populations, means and quantiles do not fit | `region R` = (region R, ∀); `population p` = (population, rate of failures ≤ p) |
| **The domain names its population** (a committed pool, or a distribution `D`) | a pool and a distribution are different claims with different assumptions (`A5`–`A7` vs `A1`); today this is hidden in `weight` | the two population cards (`population-pool`, `population-iid`) become the two domains |
| **Quantities** `M → X → [0, 1]` beside properties | calibration, Brier score and clipped log loss are means of bounded values | a property is the `{0, 1}` case |
| **Specs over two domains** | demographic parity, disparate impact, equal opportunity and version comparisons compare two populations | single-domain specs unchanged |

The full language is then

```
SPEC = AGGREGATE over DOMAIN(s) of PROPERTY or QUANTITY (of the MODEL)    with PARAMETERS
```

| Field | Closed list |
| --- | --- |
| Model (subject) | a model of a family; a tuple of models (agreement, versions); a system seen through traces; later a training procedure |
| Property / quantity | a yes/no test, or a bounded value, of the model on one input (the input may be a tuple or a trace) |
| Domain | region `R`; committed pool; distribution `D` (only through an assumption); pairs from two domains |
| Aggregate | ∀; rate ≤ p; rate ≥ q; rate ∈ [q, p]; gap ≤ ε; ratio ≥ c (two domains); mean ≤ m; quantile ≤ m; per-bin difference ≤ ε |

The guarantee stays `Sound`, with `target` = the aggregate applied to the domain.

## 3. Establishment rules

A spec is a configuration of §2; it is *checkable* when a rule proves `Sound` for its
(aggregate, domain, property class, model family). Each rule is proved once, for every property of
its class.

| # | Aggregate | Domain | Property class | Family | Method | Status |
| --- | --- | --- | --- | --- | --- | --- |
| R1 | rate ≤ p | committed pool | any decidable | any (black box) | beacon sample, exact binomial tail | proved (`poolRate_sound`) |
| R2 | rate ∈ [q, p], gap, ratio | one or two pools | any decidable | any | two rate claims per pool | statements drafted (`Specs/RateGap`) |
| R3 | rate ≤ p, graded by a judge | committed pool | judged + gold labels | any | rectifier identity | proved (`judgedRate_sound`) |
| R4 | rate ≤ p | distribution | any decidable | any | R1 + `A1-iid` | proved (`heldOut_sound`) |
| R5 | ∀ | region | prediction | ReLU MLP | integer intervals | proved (`onRegion_sound`) |
| R6 | ∀ | region | prediction, monotonicity | tree ensemble | exact per-tree check | open |
| R7 | rate ≤ p | pool of regions | prediction | ReLU MLP | R5 per item, then R1 | derivable |
| R8 | rate over pairs | two pools | ranking (AUC) | any | U-statistic tail | open |
| R9 | mean ≤ m, per-bin difference | committed pool | bounded quantity | any | bounded-mean tail | open |
| R10 | quantile ≤ m | committed pool | bounded quantity | any | order-statistic tail | open |
| R11 | ∀ | finite list | any decidable | any | enumeration | derivable |
| R12 | rate, ∀ | committed traces | trace property | system | R1 / R11 with traces as inputs | derivable |
| R13 | ∀ | every trace, at run time | trace property | system | a gate checks every action | open (rungs C2) |
| R14 | ∀ | all inputs | prediction, monotonicity | small exact models | global bounds from the weights | open |
| — | ∀ | distribution | any | any | impossible from samples | — |

## 4. Reference mapping

Each line places one known claim in the language. Coverage of the bank milestone is the test.

| Claim | Model | Input | Property / quantity | Domain | Aggregate | Rule |
| --- | --- | --- | --- | --- | --- | --- |
| error rate on production data | f | x | wrong | pool | rate ≤ p | R1 |
| held-out error (IID) | f | x | wrong | distribution | rate ≤ p | R4 |
| precision, recall, TPR, FPR | f | x | wrong, within a sub-pool | pool | rate | R1 |
| stability per window | f | x | wrong | one pool per window | rate | R1 × windows |
| AUC | f | (pos, neg) | score(pos) > score(neg) | pairs from two pools | rate | R8 |
| calibration | f | x | label, score | pool, per bin | per-bin difference | R9 |
| Brier score, clipped log loss | f | x | bounded loss | pool | mean | R9 |
| demographic parity | f | x | approved | two pools (groups) | gap | R2 |
| disparate impact (four-fifths) | f | x | approved | two pools | ratio | R2 |
| equal opportunity, equalized odds | f | x | approved | two pools of positives (and negatives) | gap(s) | R2 |
| predictive parity | f | x | correct | two pools of approvals | gap | R2 |
| individual fairness | f | (x, x') | same decision | similar pairs (region) | ∀ | R5 / R6 |
| protected feature has no influence | f | (x, x') | same decision | region varying that feature | ∀ | R5 / R6 |
| local robustness | f | x | predicts c | ball | ∀ | R5 / R6 |
| certified robust accuracy | f | x | predicts label on its ball | pool of balls | rate | R7 |
| monotonicity | f | (x, x') | x ≤ x' ⇒ f(x) ≤ f(x') | region | ∀ | R6 |
| global Lipschitz bound | f | (x, x') | distance bound | all inputs | ∀ | R14 |
| agreement with a reference, distillation fidelity | (f, g) | x | f(x) = g(x) | pool or region | rate / ∀ | R1 / R5 |
| new version no worse | (f, g) | x | wrong | one pool | gap | R2 |
| monitor detection, false-alarm rate | monitor | x | fires | pools of attacks, of benign items | rate | R1 |
| red-team success, refusal, hallucination rate | f | x | judged | pool | rate | R1 / R3 |
| label audit | labels | x | issuer ≠ gold | pool | rate | R3 |
| PII leakage, memorization | f | x | checker or judged | pool of prompts | rate | R1 / R3 |
| output schema validity | f | x | checker | every output | ∀ | R13 |
| agent never calls an unapproved tool | system | trace | always allowed | every trace | ∀ | R13 |
| agent violation rate | system | trace | violates | committed traces | rate | R12 |
| latency p99 | system | run | bounded value | pool of runs | quantile | R10 |
| circuit faithfulness | f | prompt | intervention agrees | pool | rate | R1 |
| model identity, size | artifact | — | hash, parameter count | — | — | binding, R11 |
| EU AI Act Art. 15, PRA SS1/23 | f | x, (x, x') | the lines above | pools, regions | rate, ∀ | R1, R5–R7 |
| differential privacy, unlearning | training procedure | neighbouring datasets | outputs close | — | ∀ | outside v0.1 |
| helpfulness, truthfulness | f | x | not decidable | — | — | only as a judged property (R3) |

Every claim of the bank milestone fits. Open for it: R2 (proofs), R6, R8, R9, R10.

## 5. Decisions (approved 2026-10-31)

1. A spec has **three fields**: (observable, domain, aggregate). Today's scopes are recovered as
   `region R` = (region R, ∀) and `population p` = (pool or distribution, rate ≤ p).
2. Two-domain specs use a **domain that is a pair** of populations, not a separate structure.
3. The observable is a **quantity** `M → X → [0, 1]`; a property is the `{0, 1}` case.
4. **Training-procedure claims are postponed** until a user needs them.
5. Bank order of the open rules: **R6 (trees), R2 (gap, ratio), R9 (calibration), R8 (AUC)**.
6. Ownership: the Lean skeleton (`Properties/`, `Scopes/`, `Specs/Basic`, `Specs/Instances`), the
   cards, `check_specs.py` and `specs/coverage.md` move to this language in the specs-system work;
   the rules (§3) are proved as new files stating `Sound` in this shape.
