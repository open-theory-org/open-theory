+++
id = "decision"
kind = "property"
object = "learned function"
test = "the model's binary decision on x (approve when τ ≤ score) equals c"
lean = ["OpenTheory.Checks.Tree.Ensemble.Approves"]
references = []
+++
# Property: the decision is `c`

A yes/no test of a thresholded model on one input: it approves exactly when `c`. Asked of every
input of a box, it is local robustness of the decision.
