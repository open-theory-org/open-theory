# Claim types

| Id | Claim | Lean statement | Status |
| --- | --- | --- | --- |
| `heldout-error` | With probability ≥ 1 − δ over n IID held-out examples, population error ≤ p | template `OpenTheory.HeldOut.Claim` | verified, checked by `ot verify` ([held-out error](heldout-error.md)) |
| `occam-code-error` | Same, for a model selected from a finite code family using the training data | `OpenTheory.QuantizedMLP.selected_code_certificate` | verified |
| `pacbayes-error` | Catoni PAC-Bayes bound for a posterior over a finite code space | `OpenTheory.PACBayes.catoni_pacBayes` | verified |
| `robust-accuracy` | Fraction of inputs whose prediction is constant on an ε-ball | none yet | planned (plan C2–C3) |
| `rate` | Population rate of any per-example checkable event (monitor fires, circuit faithful, policy violated) | `OpenTheory.BinomialTail.count_testSet_bound` | template planned |

`count_testSet_bound` holds for **any** measurable per-example event, so every per-example
check (white-box or behavioural) becomes a population claim through the same theorem.
