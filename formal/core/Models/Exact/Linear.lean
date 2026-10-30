import Models.Exact.Interval
import NN.GraphSpec.Chain.Primitives
import NN.Proofs.Tensor.Algebra
import NN.Proofs.Tensor.Basic.Core

/-!
# Exact linear layer

The TorchLean primitive `Primitive.linear m n` (`x ↦ W x + b`) with integer weights: its integer
runner, the agreement proof, and its interval rule.
-/

open NN.GraphSpec Spec TorchLean

namespace OpenTheory.Exact

/-- A sum over two lists of length `m`, read coordinatewise. -/
theorem sum_zipWith_eq {β γ δ : Type} [AddCommMonoid δ] (f : β → γ → δ) (db : β) (dc : γ) :
    ∀ (m : ℕ) (r : List β) (x : List γ), r.length = m → x.length = m →
      (List.zipWith f r x).sum = ∑ k : Fin m, f (r.getD k db) (x.getD k dc)
  | 0, [], [], _, _ => by simp
  | m + 1, a :: r, c :: x, hr, hx => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hr hx
      rw [Fin.sum_univ_succ, List.zipWith_cons_cons, List.sum_cons,
        sum_zipWith_eq f db dc m r x hr hx]
      simp

/-- Integer dot product. -/
def dot (r x : List ℤ) : ℤ := (List.zipWith (· * ·) r x).sum

/-- Integer parameters of a linear layer: `n` weight rows of length `m`, and `n` biases. -/
abbrev LinearParams := List (List ℤ) × List ℤ

/-- The weight matrix has `n` rows of length `m` and the bias has length `n`. -/
def linearValid (m n : ℕ) (θ : LinearParams) : Bool :=
  θ.1.length == n && θ.1.all (·.length == m) && θ.2.length == n

theorem linearValid_iff {m n : ℕ} {θ : LinearParams} :
    linearValid m n θ = true ↔
      θ.1.length = n ∧ (∀ r ∈ θ.1, r.length = m) ∧ θ.2.length = n := by
  simp [linearValid, and_assoc]

/-- Integer forward pass: `(W x + b)_i = dot (row i) x + b_i`. -/
def linearRun (θ : LinearParams) (x : List ℤ) : List ℤ :=
  List.zipWith (fun r bi => dot r x + bi) θ.1 θ.2

/-- The integer weights and bias as TorchLean tensors. -/
def linearEmbed (m n : ℕ) {α : Type} [Storage α] [Context α] (θ : LinearParams) :
    TensorPack α [[n, m], [n]] :=
  .cons (Tensor.dim fun i : Fin n => vec m (θ.1.getD i [])) (.cons (vec n θ.2) .nil)

/-- Coordinate `i` of the TorchLean linear layer over `ℝ`, on integer weights. -/
theorem linear_getScalar {m n : ℕ} (θ : LinearParams) (x : Tensor ℝ [m]) (i : Fin n) :
    ((Primitive.linear m n).specFwd (α := ℝ) (linearEmbed m n θ) x).getScalar i =
      ∑ k : Fin m, ((θ.1.getD i []).getD k 0 : ℝ) * x.getScalar k + (θ.2.getD i 0 : ℝ) := by
  simp only [Primitive.linear, linearEmbed, linearSpec]
  rw [getScalar_add_spec]
  beta_reduce
  erw [getScalar_mat_vec_mul_spec]
  simp only [get2_eq_getScalar_get, Spec.get_dim, getScalar_vec]

theorem linear_agrees {m n : ℕ} (θ : LinearParams) (x : List ℤ)
    (hθ : linearValid m n θ = true) (hx : x.length = m) :
    vec n (linearRun θ x) = (Primitive.linear m n).specFwd (α := ℝ) (linearEmbed m n θ) (vec m x) := by
  obtain ⟨hW, hrow, hb⟩ := linearValid_iff.1 hθ
  ext i
  have hiW : (i : ℕ) < θ.1.length := hW ▸ i.2
  have hib : (i : ℕ) < θ.2.length := hb ▸ i.2
  rw [linear_getScalar, getScalar_vec]
  unfold linearRun
  rw [List.getD_eq_getElem _ _ (by simp [hiW, hib]), List.getElem_zipWith, List.getD_eq_getElem _ _ hiW, List.getD_eq_getElem _ _ hib, dot,
    sum_zipWith_eq _ 0 0 m _ x (hrow _ (List.getElem_mem hiW)) hx]
  push_cast
  simp

/-! ## Interval rule -/

/-- Lower end of `w · [lo, hi]` for an integer weight `w`. -/
def lowerTerm (w : ℤ) (p : ℤ × ℤ) : ℤ := if 0 ≤ w then w * p.1 else w * p.2

/-- Upper end of `w · [lo, hi]` for an integer weight `w`. -/
def upperTerm (w : ℤ) (p : ℤ × ℤ) : ℤ := if 0 ≤ w then w * p.2 else w * p.1

theorem lowerTerm_le (w : ℤ) (p : ℤ × ℤ) {x : ℝ} (hx : (p.1 : ℝ) ≤ x ∧ x ≤ p.2) :
    (lowerTerm w p : ℝ) ≤ w * x := by
  unfold lowerTerm
  split_ifs with hw
  · push_cast; exact mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hw)
  · push_cast; exact mul_le_mul_of_nonpos_left hx.2 (by exact_mod_cast (not_le.1 hw).le)

theorem le_upperTerm (w : ℤ) (p : ℤ × ℤ) {x : ℝ} (hx : (p.1 : ℝ) ≤ x ∧ x ≤ p.2) :
    (w : ℝ) * x ≤ upperTerm w p := by
  unfold upperTerm
  split_ifs with hw
  · push_cast; exact mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hw)
  · push_cast; exact mul_le_mul_of_nonpos_left hx.1 (by exact_mod_cast (not_le.1 hw).le)

/-- Interval propagation through `x ↦ W x + b`, row by row. -/
def linearBox (θ : LinearParams) (b : Box) : Box :=
  List.zipWith (fun r bi =>
    ((List.zipWith lowerTerm r b).sum + bi, (List.zipWith upperTerm r b).sum + bi)) θ.1 θ.2

theorem linear_box_sound {m n : ℕ} (θ : LinearParams) (b : Box) (x : Tensor ℝ [m])
    (hθ : linearValid m n θ = true) (hx : InBox b x) :
    InBox (linearBox θ b) ((Primitive.linear m n).specFwd (α := ℝ) (linearEmbed m n θ) x) := by
  obtain ⟨hW, hrow, hb⟩ := linearValid_iff.1 hθ
  refine ⟨by simp [linearBox, hW, hb], fun i => ?_⟩
  have hiW : (i : ℕ) < θ.1.length := hW ▸ i.2
  have hib : (i : ℕ) < θ.2.length := hb ▸ i.2
  have hr := hrow _ (List.getElem_mem hiW)
  rw [linear_getScalar]
  unfold linearBox
  rw [List.getD_eq_getElem _ _ (by simp [hiW, hib]), List.getElem_zipWith, List.getD_eq_getElem _ _ hiW, List.getD_eq_getElem _ _ hib,
    sum_zipWith_eq _ 0 (0, 0) m _ b hr hx.1, sum_zipWith_eq _ 0 (0, 0) m _ b hr hx.1]
  push_cast
  constructor
  · gcongr with k
    exact lowerTerm_le _ _ (hx.2 k)
  · gcongr with k
    exact le_upperTerm _ _ (hx.2 k)

/-- The exact linear layer `[m] → [n]`. -/
def linear (m n : ℕ) : Prim m n where
  ps := [[n, m], [n]]
  torch := Primitive.linear m n
  Params := LinearParams
  valid := linearValid m n
  run := linearRun
  embed := linearEmbed m n
  length_run θ _ hθ _ := by
    obtain ⟨hW, -, hb⟩ := linearValid_iff.1 hθ
    simp [linearRun, hW, hb]
  agrees θ x hθ hx := linear_agrees θ x hθ hx

/-- Interval rule for the exact linear layer. -/
def linearInterval (m n : ℕ) : IntervalRule (linear m n) where
  box := linearBox
  sound θ b x hθ hx := linear_box_sound θ b x hθ hx

end OpenTheory.Exact
