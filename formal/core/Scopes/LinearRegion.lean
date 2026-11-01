import Properties.Linear
import Mathlib.Tactic.Linarith

/-!
# Linear models on a region: soundness of the checks

`robust_sound`: when `robust` accepts `c`, the model approves exactly when `c` on every real input
of the box. `monotone_sound`: when `monotone` accepts, raising feature `j` (the others fixed) moves
the score in the stated direction. Each term `w · x_f` of the score is bounded by its value at the
corner its sign picks (`termMin_le`, `le_termMax`), which is all the robustness check uses.
-/

namespace OpenTheory.Checks.Linear

open OpenTheory.Checks.Tree (Bound Box intLe intLt intLe_eq intLt_eq)

/-- `v` is within the bound. -/
def InBound (b : Bound) (v : ℝ) : Prop :=
  (∀ a, b.lo = some a → (a : ℝ) ≤ v) ∧ (∀ h, b.hi = some h → v ≤ h)

theorem termMin_le {w : Int} {b : Bound} {t : Int} {v : ℝ} (h : termMin w b = some t)
    (hv : InBound b v) : (t : ℝ) ≤ w * v := by
  unfold termMin at h
  simp only [intLe_eq, decide_eq_true_eq] at h
  by_cases h0 : (0 : Int) ≤ w
  · rw [if_pos h0] at h
    by_cases h1 : w ≤ 0
    · rw [if_pos h1] at h
      cases h
      have : w = 0 := le_antisymm h1 h0
      simp [this]
    · rw [if_neg h1] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have := hv.1 a ha
      push_cast
      exact mul_le_mul_of_nonneg_left this (by exact_mod_cast h0)
  · rw [if_neg h0] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    have := hv.2 c hc
    push_cast
    exact mul_le_mul_of_nonpos_left this (by exact_mod_cast (le_of_lt (lt_of_not_ge h0)))

theorem le_termMax {w : Int} {b : Bound} {t : Int} {v : ℝ} (h : termMax w b = some t)
    (hv : InBound b v) : (w : ℝ) * v ≤ t := by
  unfold termMax at h
  simp only [intLe_eq, decide_eq_true_eq] at h
  by_cases h0 : (0 : Int) ≤ w
  · rw [if_pos h0] at h
    by_cases h1 : w ≤ 0
    · rw [if_pos h1] at h
      cases h
      have : w = 0 := le_antisymm h1 h0
      simp [this]
    · rw [if_neg h1] at h
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
      have := hv.2 c hc
      push_cast
      exact mul_le_mul_of_nonneg_left this (by exact_mod_cast h0)
  · rw [if_neg h0] at h
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have := hv.1 a ha
    push_cast
    exact mul_le_mul_of_nonpos_left this (by exact_mod_cast (le_of_lt (lt_of_not_ge h0)))

/-- The input is within the box from feature `f` on: bound `k` of the list holds at `f + k`. -/
def MemFrom (B : Box) (f : ℕ) (x : ℕ → ℝ) : Prop := ∀ k, InBound (B.get k) (x (f + k))

theorem memFrom_nil (f : ℕ) (x : ℕ → ℝ) : MemFrom [] f x := fun _ => ⟨fun _ h => by simp [Box.get] at h, fun _ h => by simp [Box.get] at h⟩

theorem memFrom_cons {b : Bound} {B : Box} {f : ℕ} {x : ℕ → ℝ} (h : MemFrom (b :: B) f x) :
    InBound b (x f) ∧ MemFrom B (f + 1) x :=
  ⟨by simpa [Box.get] using h 0, fun k => by simpa [Box.get, Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1)⟩

theorem minScore_le : ∀ (ws : List Int) (B : Box) (f : ℕ) {x : ℕ → ℝ} {s : Int},
    MemFrom B f x → minScore ws B = some s → (s : ℝ) ≤ scoreFrom ws f x
  | [], _, _, _, s, _, h => by simp [minScore] at h; subst h; simp [scoreFrom]
  | w :: ws, [], f, x, s, hx, h => by
    simp only [minScore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, r, hr, rfl⟩ := h
    have := termMin_le ht (v := x f) ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
    have := minScore_le ws [] (f + 1) (memFrom_nil _ x) hr
    simp only [scoreFrom]; push_cast; linarith
  | w :: ws, b :: B, f, x, s, hx, h => by
    simp only [minScore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, r, hr, rfl⟩ := h
    obtain ⟨hb, hB⟩ := memFrom_cons hx
    have := termMin_le ht hb
    have := minScore_le ws B (f + 1) hB hr
    simp only [scoreFrom]; push_cast; linarith

theorem le_maxScore : ∀ (ws : List Int) (B : Box) (f : ℕ) {x : ℕ → ℝ} {s : Int},
    MemFrom B f x → maxScore ws B = some s → scoreFrom ws f x ≤ s
  | [], _, _, _, s, _, h => by simp [maxScore] at h; subst h; simp [scoreFrom]
  | w :: ws, [], f, x, s, hx, h => by
    simp only [maxScore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, r, hr, rfl⟩ := h
    have := le_termMax ht (v := x f) ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
    have := le_maxScore ws [] (f + 1) (memFrom_nil _ x) hr
    simp only [scoreFrom]; push_cast; linarith
  | w :: ws, b :: B, f, x, s, hx, h => by
    simp only [maxScore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, r, hr, rfl⟩ := h
    obtain ⟨hb, hB⟩ := memFrom_cons hx
    have := le_termMax ht hb
    have := le_maxScore ws B (f + 1) hB hr
    simp only [scoreFrom]; push_cast; linarith

theorem memFrom_of_mem {B : Box} {x : ℕ → ℝ} (hx : B.Mem x) : MemFrom B 0 x :=
  fun k => by simpa [InBound] using hx k

/-- **Robustness.** If `robust` accepts `c` on the box, the model approves an input of the box
exactly when `c`. -/
theorem robust_sound (m : LinearModel) (B : Box) (c : Bool) (h : robust m.bias m.τ m.weights B c = true)
    (x : ℕ → ℝ) (hx : B.Mem x) : (m.Approves x ↔ c = true) := by
  unfold robust at h
  unfold LinearModel.Approves LinearModel.score
  cases c with
  | true =>
    simp only [if_true] at h
    split at h
    · rename_i s hs
      simp only [intLe_eq, decide_eq_true_eq] at h
      have := minScore_le m.weights B 0 (memFrom_of_mem hx) hs
      have h' : (m.τ : ℝ) ≤ m.bias + s := by exact_mod_cast h
      simp only [iff_true]; linarith
    · simp at h
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    split at h
    · rename_i s hs
      simp only [intLt_eq, decide_eq_true_eq] at h
      have := le_maxScore m.weights B 0 (memFrom_of_mem hx) hs
      have h' : (m.bias : ℝ) + s < m.τ := by exact_mod_cast h
      simp only [Bool.false_eq_true, iff_false, not_le]; linarith
    · simp at h

theorem scoreFrom_mono (j : ℕ) {x x' : ℕ → ℝ} (hr : Raised j x x') :
    ∀ (ws : List Int) (f : ℕ), (∀ i (hi : i < ws.length), f + i = j → 0 ≤ ws[i]) →
      scoreFrom ws f x ≤ scoreFrom ws f x'
  | [], _, _ => by simp [scoreFrom]
  | w :: ws, f, hw => by
    simp only [scoreFrom]
    have tail := scoreFrom_mono j hr ws (f + 1) fun i hi hfi =>
      hw (i + 1) (by simpa using hi) (by omega)
    have head : (w : ℝ) * x f ≤ w * x' f := by
      by_cases hf : f = j
      · subst hf
        exact mul_le_mul_of_nonneg_left hr.2 (by exact_mod_cast hw 0 (by simp) (by simp))
      · rw [hr.1 f hf]
    linarith

theorem scoreFrom_anti (j : ℕ) {x x' : ℕ → ℝ} (hr : Raised j x x') :
    ∀ (ws : List Int) (f : ℕ), (∀ i (hi : i < ws.length), f + i = j → ws[i] ≤ 0) →
      scoreFrom ws f x' ≤ scoreFrom ws f x
  | [], _, _ => by simp [scoreFrom]
  | w :: ws, f, hw => by
    simp only [scoreFrom]
    have tail := scoreFrom_anti j hr ws (f + 1) fun i hi hfi =>
      hw (i + 1) (by simpa using hi) (by omega)
    have head : (w : ℝ) * x' f ≤ w * x f := by
      by_cases hf : f = j
      · subst hf
        exact mul_le_mul_of_nonpos_left hr.2 (by exact_mod_cast hw 0 (by simp) (by simp))
      · rw [hr.1 f hf]
    linarith

/-- **Monotonicity.** If `monotone` accepts, raising feature `j` (the other features fixed) never
lowers the score if `up`, never raises it otherwise. -/
theorem monotone_sound (m : LinearModel) (j : ℕ) (up : Bool) (h : monotone m.weights j up = true)
    {x x' : ℕ → ℝ} (hr : Raised j x x') : Ordered up (m.score x) (m.score x') := by
  unfold monotone at h
  unfold LinearModel.score
  cases hj : m.weights[j]? with
  | none =>
    have hlen : m.weights.length ≤ j := List.getElem?_eq_none_iff.mp hj
    have no : ∀ i (hi : i < m.weights.length), 0 + i = j → False := fun i hi hij => by omega
    cases up
    · simp only [Ordered, Bool.false_eq_true, if_false]
      linarith [scoreFrom_anti j hr m.weights 0 fun i hi hij => (no i hi hij).elim]
    · simp only [Ordered, if_true]
      linarith [scoreFrom_mono j hr m.weights 0 fun i hi hij => (no i hi hij).elim]
  | some w =>
    rw [hj] at h
    have hw : ∀ i (hi : i < m.weights.length), 0 + i = j → m.weights[i] = w := by
      intro i hi hij
      subst hij
      simpa [hi] using hj
    cases up
    · simp only [Bool.false_eq_true, if_false, intLe_eq, decide_eq_true_eq] at h
      simp only [Ordered, Bool.false_eq_true, if_false]
      linarith [scoreFrom_anti j hr m.weights 0 fun i hi hij => (hw i hi hij) ▸ h]
    · simp only [if_true, intLe_eq, decide_eq_true_eq] at h
      simp only [Ordered, if_true]
      linarith [scoreFrom_mono j hr m.weights 0 fun i hi hij => (hw i hi hij) ▸ h]

end OpenTheory.Checks.Linear
