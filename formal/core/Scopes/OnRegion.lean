import Models.Exact.Interval
import Properties.Prediction

/-!
# Scope: every input in a region

The check `certify` runs on integers in the kernel: it validates the parameters and the input
box, propagates the box through the network, and tests that the class `c` is separated in the
output box. `certify_sound`, proved once, turns acceptance into a statement about the TorchLean
model over `ℝ` on every real input in the box, together with the fact that the box is not empty.

It applies to every network whose primitives carry interval rules (`Net.Rules IntervalRule`).
-/

open TorchLean OpenTheory.Exact

namespace OpenTheory.OnRegion

/-- In the output box, the lower bound of class `c` exceeds the upper bound of every other
class. -/
def separates (out : Box) (c : ℕ) : Bool :=
  (List.range out.length).all fun j =>
    j == c || decide ((out.getD j (0, 0)).2 < (out.getD c (0, 0)).1)

/-- The region check (check form). -/
def certify {m k : ℕ} (g : Net m k) (r : g.Rules IntervalRule) (θ : g.Params) (b : Box)
    (c : Fin k) : Bool :=
  g.valid θ && b.wellFormed m && separates (g.box r θ b) c

theorem predicts_of_separates {k : ℕ} {out : Box} {y : Tensor ℝ [k]} {c : Fin k}
    (hy : InBox out y) (hsep : separates out c = true) : Predicts y c := by
  intro j hj
  simp only [separates, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hsep
  have hlt := (hsep j (hy.1 ▸ j.2)).resolve_left (fun h => hj (Fin.ext h))
  calc y.getScalar j ≤ ((out.getD j (0, 0)).2 : ℝ) := (hy.2 j).2
    _ < ((out.getD c (0, 0)).1 : ℝ) := by exact_mod_cast hlt
    _ ≤ y.getScalar c := (hy.2 c).1

/-- **Region certificate.** If `certify` accepts, the box is not empty and the TorchLean model
predicts `c` on every real input in it. -/
theorem certify_sound {m k : ℕ} (g : Net m k) (r : g.Rules IntervalRule) (θ : g.Params)
    (b : Box) (c : Fin k) (h : certify g r θ b c = true) :
    (∃ x : Tensor ℝ [m], InBox b x) ∧ ∀ x : Tensor ℝ [m], InBox b x → Predicts (g.eval θ x) c := by
  simp only [certify, Bool.and_eq_true] at h
  obtain ⟨⟨hθ, hb⟩, hsep⟩ := h
  exact ⟨⟨_, inBox_lower hb⟩, fun x hx => predicts_of_separates (Net.box_sound g r θ b x hθ hx) hsep⟩

/-! ## The ℓ∞ ball around an integer input -/

/-- The box of all inputs within integer distance `ε` of `x₀` in every coordinate. -/
def ball (x₀ : List ℤ) (ε : ℤ) : Box := x₀.map fun v => (v - ε, v + ε)

theorem inBox_ball {m : ℕ} {x₀ : List ℤ} (hx₀ : x₀.length = m) (ε : ℤ) (x : Tensor ℝ [m]) :
    InBox (ball x₀ ε) x ↔ ∀ i : Fin m, |x.getScalar i - (x₀.getD i 0 : ℝ)| ≤ ε := by
  have hlen : (ball x₀ ε).length = m := by simp [ball, hx₀]
  have hcoord : ∀ i : Fin m,
      (ball x₀ ε).getD i (0, 0) = (x₀.getD i 0 - ε, x₀.getD i 0 + ε) := fun i => by
    rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getD_eq_getElem _ _ (hx₀ ▸ i.2)]
    simp [ball]
  simp only [InBox, hlen, hcoord, true_and, abs_le]
  push_cast
  refine forall_congr' fun i => ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩ <;> linarith

/-- **Local robustness.** If `certify` accepts the ball of radius `ε` around the integer input
`x₀`, the TorchLean model predicts `c` on every real input within `ε` of `x₀` in every
coordinate. -/
theorem robust_of_certify {m k : ℕ} (g : Net m k) (r : g.Rules IntervalRule) (θ : g.Params)
    {x₀ : List ℤ} (hx₀ : x₀.length = m) {ε : ℤ} (c : Fin k)
    (h : certify g r θ (ball x₀ ε) c = true) (x : Tensor ℝ [m])
    (hx : ∀ i : Fin m, |x.getScalar i - (x₀.getD i 0 : ℝ)| ≤ ε) :
    Predicts (g.eval θ x) c :=
  (certify_sound g r θ _ c h).2 x ((inBox_ball hx₀ ε x).2 hx)

end OpenTheory.OnRegion
