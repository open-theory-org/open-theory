import Properties.Basic
import Scopes.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Specifications

A specification is an observable (a property or a quantity), a domain and an aggregate; its target
is what it asks of a model. A claim is a specification with its numbers filled in, for one model,
and a certificate is the evidence for one claim. `Specs.Instances` shows that every claim template
of the repository is an instance, with the guarantee `Sound`. See `docs/specs.md`.

Combinations without a meaning (a mean over a region, a gap over a single domain) have the target
`False`: no sound check can accept them.
-/

open MeasureTheory

namespace OpenTheory

/-- A specification: what it looks at, where, and what it asks. -/
structure Spec (M X : Type*) where
  observable : Observable M X
  domain : Domain X
  aggregate : Aggregate

namespace Observable

variable {M X : Type*}

/-- The mean of the observable over a pool or a distribution (for a property: its rate). Regions
and pairs have no mean. -/
noncomputable def mean (o : Observable M X) (m : M) : Domain X → Option ℝ
  | .pool N item => if N = 0 then none else some ((∑ j, o.value m (item j)) / N)
  | .distribution σ D =>
      letI := σ
      some (match o with
        | .property P => D.real {x | P m x}
        | .quantity Q => ∫ x, Q m x ∂D)
  | _ => none

/-- The fraction of a pool or a distribution on which the value exceeds `t`. -/
noncomputable def excess (o : Observable M X) (m : M) (t : ℝ) : Domain X → Option ℝ
  | .pool N item => if N = 0 then none else
      some ((Finset.univ.filter fun j => t < o.value m (item j)).card / N)
  | .distribution σ D =>
      letI := σ
      some (D.real {x | t < o.value m x})
  | _ => none

end Observable

/-- What the spec asks of the model `m`. -/
def Spec.Target {M X : Type*} (σ : Spec M X) (m : M) : Prop :=
  match σ.aggregate, σ.domain with
  | .all, d => d.All (σ.observable.Holds m)
  | .meanLe a, d => ∃ μ, σ.observable.mean m d = some μ ∧ μ ≤ a
  | .meanGe a, d => ∃ μ, σ.observable.mean m d = some μ ∧ a ≤ μ
  | .quantileLe α t, d => ∃ f, σ.observable.excess m t d = some f ∧ f ≤ 1 - α
  | .gapLe ε, .pair d₁ d₂ => ∃ μ₁ μ₂, σ.observable.mean m d₁ = some μ₁ ∧
      σ.observable.mean m d₂ = some μ₂ ∧ |μ₁ - μ₂| ≤ ε
  | .ratioGe c, .pair d₁ d₂ => ∃ μ₁ μ₂, σ.observable.mean m d₁ = some μ₁ ∧
      σ.observable.mean m d₂ = some μ₂ ∧ c * μ₂ ≤ μ₁
  | _, _ => False

/-! ## Targets in the forms the instances use -/

@[simp] theorem Spec.target_all_region {M X : Type*} (P : Property M X) (R : Set X) (m : M) :
    (⟨.property P, .region R, .all⟩ : Spec M X).Target m ↔ ∀ x ∈ R, P m x := Iff.rfl

/-- A property's rate on a distribution. -/
@[simp] theorem Spec.target_meanLe_distribution {M X : Type*} [σ : MeasurableSpace X]
    (P : Property M X) (D : Measure X) (p : ℝ) (m : M) :
    (⟨.property P, .distribution σ D, .meanLe p⟩ : Spec M X).Target m ↔ D.real {x | P m x} ≤ p := by
  simp [Spec.Target, Observable.mean]

open Classical in
/-- A property's rate on a pool is the fraction of items where it holds. -/
@[simp] theorem Spec.target_meanLe_pool {M X : Type*} {N : ℕ} [NeZero N] (P : Property M X)
    (item : Fin N → X) (p : ℝ) (m : M) :
    (⟨.property P, .pool N item, .meanLe p⟩ : Spec M X).Target m ↔
      ((Finset.univ.filter fun j => P m (item j)).card : ℝ) / N ≤ p := by
  classical
  simp [Spec.Target, Observable.mean, Observable.value, NeZero.ne N, Finset.sum_boole]

end OpenTheory
