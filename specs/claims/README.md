# Claim types

| Id | Claim | Lean statement | Status |
| --- | --- | --- | --- |
| `heldout-error` | With probability ≥ 1 − δ over n IID held-out examples, population error ≤ p | template `OpenTheory.HeldOut.Claim` | verified, checked by `ot verify` ([held-out error](heldout-error.md)) |
| `occam-code-error` | Same, for a model selected from a finite code family using the training data | `OpenTheory.QuantizedMLP.selected_code_certificate` | verified |
| `pacbayes-error` | Catoni PAC-Bayes bound for a posterior over a finite code space | `OpenTheory.PACBayes.catoni_pacBayes` | verified |
| `pool-rate` | Fraction of a committed pool failing a committed procedure, sample chosen by a public beacon after commitment; no distributional assumption | template `OpenTheory.PoolRate.Claim`, meaning `OpenTheory.DesignSampling.rate_sound` | verified, checked by `ot verify` ([pool rate](pool-rate.md)) |
| `judged-rate` | Fraction of a committed pool failing against gold labels, from a committed AI judge (or the issuer's labels) on a large beacon sample and gold labels on a small prefix: exact finite-sample prediction-powered inference | template `OpenTheory.JudgedRate.Claim`, meaning `JudgedRate.Claim.sound`, `Claim.sound_alarms`, `JudgedRate.bad_frac` | verified, checked by `ot verify` ([judged rate](judged-rate.md)) |
| `robust-accuracy` | Fraction of inputs whose prediction is constant on an ε-ball | none yet | planned (plan C2–C3) |
| `rate` | Population rate of any per-example checkable event (monitor fires, circuit faithful, policy violated) | `OpenTheory.BinomialTail.count_testSet_bound` | template planned |

`count_testSet_bound` holds for **any** measurable per-example event, so every per-example
check (white-box or behavioural) becomes a population claim through the same theorem.
