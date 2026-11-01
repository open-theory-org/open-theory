+++
id = "relu-mlp"
family = "ReLU MLPs of any depth and widths with integer weights, as TorchLean chains"
type = "OpenTheory.Exact.Net.Params"     # the Lean type a spec quantifies over (Spec M X: M)
lean = ["OpenTheory.Exact.reluMLP", "OpenTheory.Exact.Net"]
references = [{ key = "torchlean", relation = "background" }]
+++
# Model: ReLU MLP

Built from exact `linear` and `relu` primitives. Agreement with TorchLean (`Net.agrees`) and
interval soundness (`Net.box_sound`) are proved once for the whole family.
