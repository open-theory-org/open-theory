+++
id = "monotone"
kind = "property"
object = "learned function"
test = "on a pair (x, x') differing only in feature j with x_j ≤ x'_j, the score does not decrease (or, decreasing, does not increase)"
lean = ["OpenTheory.MonotoneIn", "OpenTheory.Raised", "OpenTheory.Ordered", "OpenTheory.HasScore"]
needs = ["OpenTheory.HasScore"]
references = [{ key = "devos2021versatile", relation = "background" }]
+++
# Property: monotone in feature `j`

A yes/no test on a **pair** of inputs: if `x'` raises feature `j` of `x` and keeps every other
feature, the score moves in the stated direction. Stated once (`MonotoneIn`) for every family with a score
(`HasScore`). Asked of every pair in a box, it is monotonicity
of the model in `j` on the box (for example, a higher income never lowers a credit score).
