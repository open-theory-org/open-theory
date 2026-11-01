+++
id = "quantized-mlp"
family = "one-hidden-layer ReLU MLP with 2-bit integer codes"
type = "OpenTheory.QuantizedMLP.Code"     # the Lean type a spec quantifies over (Spec M X: M)
implements = []   # instances in Properties/ (the properties it can be asked)
lean = ["OpenTheory.QuantizedMLP.scoresOfWeights", "OpenTheory.QuantizedMLP.scoresPacked", "OpenTheory.QuantizedMLP.asNet", "OpenTheory.QuantizedMLP.scoresOfWeights_eq_run"]
references = []
+++
# Model: quantized MLP

The repository's first certified model: integer codes in `{-2, …, 1}`, evaluated exactly by the
kernel (list or packed form, proved equal).

**A member of the ReLU-network family.** Read as parameters of `Exact.reluMLP d [h] c`, its
scores are that network's integer forward pass (`scoresOfWeights_eq_run`,
`Models/QuantizedMLP/Net.lean`), so the facts proved once for `Exact.Net` apply to it.
