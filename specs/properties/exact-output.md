+++
kind = "property"
id = "exact-output"
object = "learned function"
test = "the network outputs exactly Y on the input x"
lean = ["OpenTheory.Exact.Net.OutputIs"]
needs = []
references = [{ key = "harvey2009kronecker", relation = "background" }]
+++
# Property: exact output

The network's integer forward pass on `x` gives exactly the claimed scores `Y`
(`Exact.Net.OutputIs`, `Properties/Network.lean`). For valid parameters it is also the TorchLean
model's output over ℝ (`Net.agrees`).
