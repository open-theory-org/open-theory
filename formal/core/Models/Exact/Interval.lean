import Models.Exact.Basic

/-!
# Interval contract

An `IntervalRule` for a primitive maps integer bounds on its input to integer bounds on its
output, and is sound for the TorchLean semantics over `ℝ`: every real input inside the input box
is sent inside the output box. `Net.box_sound` lifts this to every network whose primitives all
carry a rule, by one induction on the composition.

Bounds stay integral because weights are integers, so the check runs in the kernel on `ℤ`
while the guarantee covers every real input in the box.
-/

open NN.GraphSpec Spec TorchLean

namespace OpenTheory.Exact

/-- Integer bounds `(lo, hi)`, one pair per coordinate. -/
abbrev Box := List (ℤ × ℤ)

/-- The real vector `x` lies in `b`: `b` has one pair per coordinate and `lo_i ≤ x_i ≤ hi_i`. -/
def InBox {n : ℕ} (b : Box) (x : Tensor ℝ [n]) : Prop :=
  b.length = n ∧ ∀ i : Fin n,
    ((b.getD i (0, 0)).1 : ℝ) ≤ x.getScalar i ∧ x.getScalar i ≤ ((b.getD i (0, 0)).2 : ℝ)

/-- `b` has `n` pairs, each with `lo ≤ hi`: the box is not empty (`inBox_lower`). -/
def Box.wellFormed (b : Box) (n : ℕ) : Bool :=
  b.length == n && b.all fun p => decide (p.1 ≤ p.2)

/-- A well-formed box contains its lower corner, so a certificate about it is never vacuous. -/
theorem inBox_lower {b : Box} {n : ℕ} (hb : b.wellFormed n = true) :
    InBox b (vec n (b.map Prod.fst)) := by
  simp only [Box.wellFormed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    at hb
  refine ⟨hb.1, fun i => ?_⟩
  have hi : (i : ℕ) < b.length := hb.1 ▸ i.2
  have hlo : (b.map Prod.fst).getD i 0 = b[(i : ℕ)].1 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  simp only [getScalar_vec, hlo, List.getD_eq_getElem _ _ hi]
  exact ⟨le_rfl, by exact_mod_cast hb.2 _ (List.getElem_mem hi)⟩

/-- Interval contract for one primitive: an integer bound rule that is sound for the TorchLean
semantics over `ℝ` on every real input in the box. -/
structure IntervalRule {m n : ℕ} (p : Prim m n) where
  /-- Output bounds from input bounds. -/
  box : p.Params → Box → Box
  sound : ∀ θ b (x : Tensor ℝ [m]), p.valid θ = true → InBox b x →
    InBox (box θ b) (p.torch.specFwd (α := ℝ) (p.embed θ) x)

namespace Net

/-- Interval bound propagation through the network (check form). -/
def box : {m n : ℕ} → (g : Net m n) → g.Rules IntervalRule → g.Params → Box → Box
  | _, _, prim _, r, θ, b => r.box θ b
  | _, _, seq f g, r, θ, b => g.box r.2 θ.2 (f.box r.1 θ.1 b)

/-- **Interval soundness for every network** whose primitives carry interval rules: every real
input in `b` is sent by the TorchLean model into `g.box r θ b`. -/
theorem box_sound : {m n : ℕ} → (g : Net m n) → (r : g.Rules IntervalRule) →
    ∀ θ b (x : Tensor ℝ [m]), g.valid θ = true → InBox b x → InBox (g.box r θ b) (g.eval θ x)
  | _, _, prim _, r, θ, b, x, hθ, hx => by
      simpa [box, eval, toChain, embed, Interp.spec] using r.sound θ b x hθ hx
  | _, _, seq f g, r, θ, b, x, hθ, hx => by
      simp only [valid, Bool.and_eq_true] at hθ
      have h := g.box_sound r.2 θ.2 _ _ hθ.2 (f.box_sound r.1 θ.1 b x hθ.1 hx)
      simpa [box, eval, toChain, embed, Interp.spec, TensorPack.split_append] using h

end Net

end OpenTheory.Exact
