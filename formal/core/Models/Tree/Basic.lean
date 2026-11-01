import Checks.Tree
import Mathlib.Basic.Real.Basic

/-!
# Tree ensembles: exact semantics

The proof form of the tree ensembles of `Checks/Tree.lean`: the same data, read over real inputs.
An input is a real vector indexed by feature (`ℕ → ℝ`); thresholds and leaves are the integers of
the check form, so the two forms need no agreement theorem. The certificate producer scales each
feature by a positive factor so that the model's thresholds become integers, and the leaves by a
common positive factor; both scalings leave every decision unchanged.
-/

namespace OpenTheory.Checks.Tree

/-- The leaf value an input reaches. -/
noncomputable def Tree.eval : Tree → (ℕ → ℝ) → ℝ
  | .leaf v, _ => v
  | .node f t l r, x => if x f ≤ t then l.eval x else r.eval x

/-- A tree ensemble that approves when `τ ≤ base + Σ trees`. -/
structure Ensemble where
  base : Int
  τ : Int
  trees : List Tree

/-- The ensemble's score on an input. -/
noncomputable def Ensemble.score (e : Ensemble) (x : ℕ → ℝ) : ℝ :=
  e.base + (e.trees.map fun t => t.eval x).sum

/-- The ensemble approves the input. -/
def Ensemble.Approves (e : Ensemble) (x : ℕ → ℝ) : Prop := (e.τ : ℝ) ≤ e.score x

/-- The input lies in the box: within every bound the box states. -/
def Box.Mem (B : Box) (x : ℕ → ℝ) : Prop :=
  ∀ f, (∀ a, (B.get f).lo = some a → (a : ℝ) ≤ x f) ∧ (∀ b, (B.get f).hi = some b → x f ≤ b)

end OpenTheory.Checks.Tree
