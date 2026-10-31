+++
kind = "property"
id = "predicts"
object = "learned function"
test = "the model's scores rank class c strictly above every other class on x"
lean = ["OpenTheory.Predicts"]
references = []
+++
# Property: predicts class `c`

A yes/no test on one model output. Strictness avoids any convention for ties.
