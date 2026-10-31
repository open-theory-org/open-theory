+++
id = "exact-output"
object = "learned function"
test = "the network outputs exactly Y on the input x"
lean = ["OpenTheory.Checks.MLP.check"]
references = [{ key = "harvey2009kronecker", relation = "background" }]
+++
# Property: exact output

The network's integer forward pass on `x` gives exactly the claimed scores `Y`.
