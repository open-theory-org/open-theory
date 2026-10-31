import Properties.Basic
import Scopes.Basic

/-!
# Specifications

A specification is a property together with its scope; its target is what it asks of a model. A
claim is a specification with its numbers filled in, for one model, and a certificate is the
evidence for one claim. `Specs.Instances` shows that every claim template of the repository is an
instance of this construction, with the guarantee `Sound`. See `docs/specs.md`.
-/

namespace OpenTheory

/-- A specification: a property together with its scope. -/
structure Spec (M X : Type*) where
  property : Property M X
  scope : Scope X

/-- What the spec asks of the model `m`. `weight S` is the fraction of the population in `S`
(`D.real` for a distribution `D`, the pool fraction for a finite pool); only `population`
scopes use it. -/
def Spec.Target {M X : Type*} (σ : Spec M X) (m : M) (weight : Set X → ℝ) : Prop :=
  match σ.scope with
  | .region R => ∀ x ∈ R, σ.property m x
  | .population p => weight {x | ¬ σ.property m x} ≤ p

@[simp] theorem Spec.target_region {M X : Type*} (P : Property M X) (R : Set X) (m : M)
    (w : Set X → ℝ) : (⟨P, .region R⟩ : Spec M X).Target m w ↔ ∀ x ∈ R, P m x := Iff.rfl

@[simp] theorem Spec.target_population {M X : Type*} (P : Property M X) (p : ℝ) (m : M)
    (w : Set X → ℝ) : (⟨P, .population p⟩ : Spec M X).Target m w ↔ w {x | ¬ P m x} ≤ p := Iff.rfl

end OpenTheory
