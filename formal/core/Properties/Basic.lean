/-!
# Properties

A property is a yes/no test of a model on one input. It is the basic unit of every claim: a scope
(`Scopes.Basic`) says on which inputs it must hold, and the pair is a specification
(`Specs.Basic`). See `docs/specs.md`.
-/

universe u v

namespace OpenTheory

/-- A property: a yes/no test of the model `m` on one input `x`. -/
abbrev Property (M : Type u) (X : Type v) := M → X → Prop

end OpenTheory
