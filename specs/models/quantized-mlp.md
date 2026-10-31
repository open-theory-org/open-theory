+++
id = "quantized-mlp"
family = "one-hidden-layer ReLU MLP with 2-bit integer codes"
lean = ["OpenTheory.QuantizedMLP.scoresOfWeights", "OpenTheory.QuantizedMLP.scoresPacked"]
references = []
+++
# Model: quantized MLP

The repository's first certified model: integer codes in `{-2, …, 1}`, evaluated exactly by the
kernel (list or packed form, proved equal).
