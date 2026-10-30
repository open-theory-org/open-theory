import Models.Exact.Interval
import NN.GraphSpec.Chain.Primitives

/-!
# Exact ReLU

The TorchLean primitive `Primitive.relu [n]` on integer vectors: its integer runner, the
agreement proof, and its interval rule.
-/

open NN.GraphSpec Spec TorchLean

namespace OpenTheory.Exact

/-- TorchLean's scalar ReLU over `ℝ` is `max x 0`. -/
theorem reluSpec_real (x : ℝ) : Activation.Math.reluSpec x = max x 0 := by
  unfold Activation.Math.reluSpec
  split_ifs with h
  · simp only [beq_iff_eq] at h; rw [h, max_self]
  · rfl

/-- Coordinate `i` of the TorchLean ReLU over `ℝ`. -/
theorem relu_getScalar {n : ℕ} (x : Tensor ℝ [n]) (i : Fin n) :
    ((Primitive.relu [n]).specFwd (α := ℝ) TensorPack.nil x).getScalar i =
      max (x.getScalar i) 0 := by
  simp only [Primitive.relu, Activation.reluSpec, TorchLean.Tensor.getScalar_map, reluSpec_real]

theorem relu_agrees (n : ℕ) (x : List ℤ) :
    vec n (x.map (max · 0)) = (Primitive.relu [n]).specFwd (α := ℝ) TensorPack.nil (vec n x) := by
  ext i
  rw [relu_getScalar, getScalar_vec, getScalar_vec]
  have hmap : (x.map (max · 0)).getD i 0 = max (x.getD i 0) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x[(i : ℕ)]? <;> simp
  rw [hmap]
  push_cast
  rfl

/-- Interval propagation through ReLU: `[lo, hi] ↦ [max lo 0, max hi 0]`. -/
def reluBox (b : Box) : Box := b.map fun p => (max p.1 0, max p.2 0)

theorem relu_box_sound {n : ℕ} (b : Box) (x : Tensor ℝ [n]) (hx : InBox b x) :
    InBox (reluBox b) ((Primitive.relu [n]).specFwd (α := ℝ) TensorPack.nil x) := by
  refine ⟨by simp [reluBox, hx.1], fun i => ?_⟩
  have hi : (i : ℕ) < b.length := hx.1 ▸ i.2
  have h := hx.2 i
  rw [List.getD_eq_getElem _ _ hi] at h
  rw [relu_getScalar, List.getD_eq_getElem _ _ (by simpa [reluBox] using hi)]
  simp only [reluBox, List.getElem_map]
  push_cast
  exact ⟨max_le_max_right 0 h.1, max_le_max_right 0 h.2⟩

/-- The exact ReLU on vectors of length `n`. -/
def relu (n : ℕ) : Prim n n where
  ps := []
  torch := Primitive.relu [n]
  Params := Unit
  valid _ := true
  run _ x := x.map (max · 0)
  embed _ := TensorPack.nil
  length_run _ _ _ hx := by simpa using hx
  agrees _ x _ _ := relu_agrees n x

/-- Interval rule for the exact ReLU. -/
def reluInterval (n : ℕ) : IntervalRule (relu n) where
  box _ := reluBox
  sound _ b x _ hx := relu_box_sound b x hx

end OpenTheory.Exact
