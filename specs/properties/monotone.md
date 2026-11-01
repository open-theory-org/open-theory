+++
id = "monotone"
kind = "property"
object = "learned function"
test = "on a pair (x, x') differing only in feature j with x_j ≤ x'_j, the score does not decrease (or, decreasing, does not increase)"
lean = ["OpenTheory.Checks.Tree.Raised", "OpenTheory.Checks.Tree.Ordered"]
references = [{ key = "devos2021versatile", relation = "background" }]
+++
# Property: monotone in feature `j`

A yes/no test on a **pair** of inputs: if `x'` raises feature `j` of `x` and keeps every other
feature, the score moves in the stated direction. Asked of every pair in a box, it is monotonicity
of the model in `j` on the box (for example, a higher income never lowers a credit score).
