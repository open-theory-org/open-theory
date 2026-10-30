import NN.Spec.Core.Tensor.Core
import Mathlib.Basic.Real.Basic

/-!
# Prediction

A yes/no test on one model output: the score vector `y` predicts class `c` with a strict
margin. Strictness avoids any convention for ties.
-/

open TorchLean

namespace OpenTheory

/-- The scores `y` predict class `c`: every other score is strictly lower. -/
def Predicts {k : ℕ} (y : Tensor ℝ [k]) (c : Fin k) : Prop :=
  ∀ j : Fin k, j ≠ c → y.getScalar j < y.getScalar c

end OpenTheory
