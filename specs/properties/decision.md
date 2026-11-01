+++
id = "decision"
kind = "property"
object = "learned function"
test = "the model's decision on x is y"
lean = ["OpenTheory.Decides", "OpenTheory.HasDecision"]
needs = ["OpenTheory.HasDecision"]
references = []
+++
# Property: the decision is `y`

A yes/no test of a model on one input: the model decides `y` on `x`. Stated once
(`Decides`, `Properties/Interface.lean`) for every family that says what it decides:

| Family | Decision |
| --- | --- |
| tree ensembles | approve (`true`) when `τ ≤ score` |
| ReLU networks | the class its scores rank strictly first (`Predicts`; strictness avoids any tie rule) |

Asked of every input of a box, it is local robustness of the decision (`robust-decision`).
