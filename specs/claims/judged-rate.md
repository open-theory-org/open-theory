+++
id = "judged-rate"
observable = "event"
domain = "pool"
aggregate = "meanLe"
models = ["any-system"]
lean = ["OpenTheory.JudgedRate.Claim"]
claim_types = ["OpenTheory.ClaimTypes.judgedRate", "OpenTheory.ClaimTypes.judgedRateAlarms"]
assumptions = ["A5-beacon", "A6-timestamp", "A7-issuer-identity", "A12-commitment-binding", "A9-gold-labels"]
references = [{ key = "clopper1934use", relation = "implements" }]
+++
# Claim: judged rate (`judged-rate`, v0.1)

**Statement.** An issuer commits to a pool of `N` items, each with a logged `output` and the
`judge` label of a cheap grader: an AI judge, or the issuer's own labels (a label audit). A public
seed published after the commitment selects `n` items; an independent labeller supplies gold labels
for the first `m ≤ n` of them. Three rate claims are read off the sample:

| Part | Bits | Sample | Bounds |
| --- | --- | --- | --- |
| `judge` | the judge fails the item (`output ≠ judge`) | all `n` | judged rate ≤ `pJ` |
| `audit` | gold fails it, the judge passed it (missed) | first `m` | missed rate ≤ `pA` |
| `alarms` (optional) | not (gold passes it and the judge failed it) | first `m` | false-alarm rate ≥ `1 − pB` |

Then the fraction of the pool whose output differs from its gold label is at most `pJ + pA`, or
`pJ + pA + pB − 1` with `alarms`, except on a set of seeds of fraction at most
`(1 + N/2²⁵⁶)ⁿ δJ + (1 + N/2²⁵⁶)ᵐ (δA + δB)`.

**Why it is tight.** The rectifier identity `true = judged + missed − false alarms` holds exactly
on the pool (`DesignSampling.poolRate_rectify`). Gold labels only pay for the judge's errors, which
are rare when the judge is good; the model's own error rate is estimated from the large judged
sample. This is prediction-powered inference made exact and finite-sample: three Clopper–Pearson
(or Chernoff-witness) bounds and a union bound, with no asymptotics. It is always at least as tight
as the triangle bound `true ≤ judged + P(judge ≠ gold)`, since a missed failure is a disagreement.

**Lean.** `OpenTheory.JudgedRate.Claim` in `formal/core/Specs/JudgedRate.lean`. Meaning:
`Claim.sound` (without `alarms`) and `Claim.sound_alarms`, with `bad_frac` for the seeds; the gold
sample is a prefix of the judged one, sound by `DesignSampling.seedFrac_prefix`. Each part is checked
by `Checks.poolCheck` (or `poolCheckWitness`) and turned into a claim by `PoolRate.Claim.of_poolCheck`.

## Protocol

As [`pool-rate`](pool-rate.md), with procedure kind `judged-exact-match`: every pool item carries
`output` and `judge`, committed before the round, and `commitment.sample.audit` fixes
`{m, delta_missed, delta_alarms?}`. `sample.json` adds `gold`, the gold labels of the first `m`
sampled items. The claim has parts `judge`, `audit` and optionally `alarms`, each
`{count, bound, witness?}`; the δ of each part is the committed one.

## Verifier checks

Steps 1–3 and 6 of `pool-rate`. Then: every judge verdict recomputed from the committed labels, the
first `m` items graded against `gold`, the three bit vectors checked by the decision procedure
(in the kernel; `--compiled` runs them as compiled code, not verified), and the bound reported as an exact fraction.
The report also prints the gold-only failure rate on the audited items, for comparison.

## Assumptions

`A5-beacon`, `A6-timestamp`, `A7-issuer-identity`, `A9-gold-labels`. The judge needs no
assumption: a bad judge loosens the bound, it never makes it wrong.

## Does not cover

- Items outside the committed pool (future traffic, distribution shift).
- Whether the gold labels are right: the rate is relative to them (`A9`).
- Commitments the issuer made to the same round and did not declare (`A7`).

## Prior art

Prediction-powered inference [@angelopoulos2023prediction] and
its finite-sample variants combine model-predicted labels with a small gold set. New here: an exact
finite-sample bound for a failure rate on a committed pool, from Clopper–Pearson parts, proved in
Lean and checked per certificate by a decision procedure.
