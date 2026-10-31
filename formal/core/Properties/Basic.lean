import Mathlib.Basic.Real.Basic

/-!
# Observables

What a specification looks at: a property (a yes/no test of a model on one input) or a quantity
(a value of the model on one input, in `[0, 1]`: a bounded loss, a score). A property's value is
`1` where it holds and `0` elsewhere, so its mean over a population is its rate. The input may be a
tuple (a pair `(x, x')` for monotonicity or fairness, a pair `(pos, neg)` for AUC) or a trace:
`X` is any type. A domain and an aggregate (`Scopes.Basic`) complete the specification
(`Specs.Basic`). See `docs/specs.md`.
-/

namespace OpenTheory

/-- A property: a yes/no test of the model `m` on one input `x`. -/
abbrev Property (M X : Type*) := M → X → Prop

/-- A quantity: a value of the model `m` on one input `x`, meant to lie in `[0, 1]`. -/
abbrev Quantity (M X : Type*) := M → X → ℝ

/-- What a specification looks at. -/
inductive Observable (M X : Type*) where
  | property (P : Property M X)
  | quantity (Q : Quantity M X)

namespace Observable

variable {M X : Type*}

/-- The value of the observable: `1` or `0` for a property, the quantity itself otherwise. -/
noncomputable def value : Observable M X → M → X → ℝ
  | .property P, m, x => by classical exact if P m x then 1 else 0
  | .quantity Q, m, x => Q m x

/-- The observable holds on `x`: the property holds, or the quantity is `1`. -/
def Holds : Observable M X → M → X → Prop
  | .property P, m, x => P m x
  | .quantity Q, m, x => Q m x = 1

end Observable

end OpenTheory
