import Models.Exact.MLP
import Scopes.OnRegion

/-! Smoke tests for exact integer networks: agreement with TorchLean, kernel speed, and the
region certificate (one accepted radius, one correctly refused). -/

open TorchLean OpenTheory.Exact OpenTheory.OnRegion

namespace ExactNetSmoke

/-! ## Agreement: a kernel run becomes a statement about the TorchLean model -/

/-- `4 → 2 → 1`, mixed-sign weights so ReLU matters. -/
abbrev small : Net 4 1 := reluMLP 4 [2] 1

def θsmall : small.Params :=
  ((([[1, -2, 3, 0], [-1, 1, -1, 1]], [1, 0]), ()), ([[2, 5]], [-3]))

theorem small_valid : small.valid θsmall = true := by decide +kernel

-- Hidden layer [1 - 4 + 9 + 0 + 1, -1 + 2 - 3 + 4 + 0] = [7, 2]; output 2·7 + 5·2 - 3 = 21.
theorem small_run : small.run θsmall [1, 2, 3, 4] = [21] := by decide +kernel

theorem small_eval : small.eval θsmall (vec 4 [1, 2, 3, 4]) = vec 1 [21] := by
  rw [← Net.agrees small θsmall _ small_valid rfl, small_run]

/-! ## Speed: an MNIST-sized member, `784 → 128 → 10` (about 100k multiplications) -/

def ones (m n : ℕ) : LinearParams := (List.replicate n (List.replicate m 1), List.replicate n 0)

abbrev big : Net 784 10 := reluMLP 784 [128] 10

def θbig : big.Params := ((ones 784 128, ()), ones 128 10)

theorem big_run : big.run θbig (List.replicate 784 1) = List.replicate 10 100352 := by
  decide +kernel

/-! ## Region certificate -/

/-- Scores `[relu x₀ - relu x₁, relu x₁ - relu x₀]`: class 0 iff `relu x₀ > relu x₁`. -/
abbrev cls : Net 2 2 := reluMLP 2 [2] 2

def θcls : cls.Params := ((([[1, 0], [0, 1]], [0, 0]), ()), ([[1, -1], [-1, 1]], [0, 0]))

-- Radius 3 around [10, 2]: hidden boxes [7, 13] and [0, 5]; score 0 ≥ 7 - 5 = 2 > score 1 ≤ -2.
theorem certified : certify cls (reluMLP.intervalRules 2 [2] 2) θcls (ball [10, 2] 3) 0 = true := by
  decide +kernel

/-- Every real input within 3 of `[10, 2]` in each coordinate is classified as 0 by the
TorchLean model. -/
theorem robust (x : Tensor ℝ [2])
    (hx : ∀ i : Fin 2, |x.getScalar i - (([10, 2] : List ℤ).getD i 0 : ℝ)| ≤ ((3 : ℤ) : ℝ)) :
    OpenTheory.Predicts (cls.eval θcls x) 0 :=
  robust_of_certify cls _ θcls rfl 0 certified x hx

-- Radius 5 is refused, and rightly: [5, 7] lies in that ball and is classified as 1.
theorem refused : certify cls (reluMLP.intervalRules 2 [2] 2) θcls (ball [10, 2] 5) 0 = false := by
  decide +kernel

theorem refused_is_right : cls.run θcls [5, 7] = [-2, 2] := by decide +kernel

end ExactNetSmoke

#print axioms ExactNetSmoke.small_eval
#print axioms ExactNetSmoke.big_run
#print axioms ExactNetSmoke.robust
#print axioms ExactNetSmoke.refused
