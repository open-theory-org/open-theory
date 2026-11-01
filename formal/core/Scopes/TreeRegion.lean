import Properties.Tree
import Mathlib.Tactic.Linarith

/-!
# Tree ensembles on a region: soundness of the checks

`robustCert_sound`: when the robustness certificate is accepted for `c`, the ensemble approves
exactly when `c` on every real input of the box. `monotoneCert_sound`: when the monotonicity
certificate is accepted, the score is monotone in feature `j` between any two inputs of the box
that differ only in `j`. Both proved once, for every ensemble
and box. The sufficient condition for monotonicity (each tree monotone) follows Devos et al.
[@devos2021versatile]; the box bounds on leaves are the per-tree step of exact robustness
checking [@chen2019robustness].
-/

namespace OpenTheory.Checks.Tree

variable {B : Box} {x : ℕ → ℝ} {f : ℕ} {t : Int}

theorem lowOk_of_mem (hx : B.Mem x) (h : x f ≤ t) : lowOk B f t = true := by
  unfold lowOk
  split
  · rfl
  · rename_i a ha
    have := (hx f).1 a ha
    simpa using (show (a : ℝ) ≤ t from this.trans h)

theorem highOk_of_mem (hx : B.Mem x) (h : (t : ℝ) < x f) : highOk B f t = true := by
  unfold highOk
  split
  · rfl
  · rename_i b hb
    have := (hx f).2 b hb
    simpa using (show (t : ℝ) < b from h.trans_le this)

/-- A leaf bound that passes `allLe` bounds every leaf a point of the box reaches. -/
theorem allLe_sound (T : Tree) {m : Int} (h : T.allLe B m = true) (hx : B.Mem x) : T.eval x ≤ m := by
  induction T with
  | leaf v => simpa [Tree.allLe, Tree.eval] using h
  | node f t l r ihl ihr =>
    simp only [Tree.allLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    unfold Tree.eval
    by_cases hf : x f ≤ t
    · rw [if_pos hf]
      exact ihl (by simpa [lowOk_of_mem hx hf] using h.1)
    · rw [if_neg hf]
      exact ihr (by simpa [highOk_of_mem hx (lt_of_not_ge hf)] using h.2)

theorem allGe_sound (T : Tree) {m : Int} (h : T.allGe B m = true) (hx : B.Mem x) : (m : ℝ) ≤ T.eval x := by
  induction T with
  | leaf v => simpa [Tree.allGe, Tree.eval] using h
  | node f t l r ihl ihr =>
    simp only [Tree.allGe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    unfold Tree.eval
    by_cases hf : x f ≤ t
    · rw [if_pos hf]
      exact ihl (by simpa [lowOk_of_mem hx hf] using h.1)
    · rw [if_neg hf]
      exact ihr (by simpa [highOk_of_mem hx (lt_of_not_ge hf)] using h.2)

theorem withinAll_hi (ts : List Tree) (ms : List Int) (h : withinAll B true ts ms = true)
    (hx : B.Mem x) : (ts.map fun t => t.eval x).sum ≤ sumInt ms := by
  induction ts generalizing ms with
  | nil => cases ms <;> simp_all [withinAll, sumInt]
  | cons t ts ih =>
    cases ms with
    | nil => simp [withinAll] at h
    | cons m ms =>
      simp only [withinAll, if_true, Bool.and_eq_true] at h
      simp only [List.map_cons, List.sum_cons, sumInt]; push_cast
      exact add_le_add (allLe_sound t h.1 hx) (ih ms h.2)

theorem withinAll_lo (ts : List Tree) (ms : List Int) (h : withinAll B false ts ms = true)
    (hx : B.Mem x) : (sumInt ms : ℝ) ≤ (ts.map fun t => t.eval x).sum := by
  induction ts generalizing ms with
  | nil => cases ms <;> simp_all [withinAll, sumInt]
  | cons t ts ih =>
    cases ms with
    | nil => simp [withinAll] at h
    | cons m ms =>
      simp only [withinAll, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
      simp only [List.map_cons, List.sum_cons, sumInt]; push_cast
      exact add_le_add (allGe_sound t h.1 hx) (ih ms h.2)

/-- **Robustness.** If the robustness certificate is accepted for `c` on the box, the ensemble
approves an input of the box exactly when `c`. -/
theorem robustCert_sound (e : Ensemble) (ms : List Int) (B : Box) (c : Bool)
    (h : robustCert e.base e.τ e.trees ms B c = true) (x : ℕ → ℝ) (hx : B.Mem x) :
    (e.Approves x ↔ c = true) := by
  unfold robustCert at h
  unfold Ensemble.Approves Ensemble.score
  cases c with
  | true =>
    simp only [if_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true] at h
    have := withinAll_lo e.trees ms h.2 hx
    have h' : ((e.τ : Int) : ℝ) ≤ (e.base : ℝ) + (sumInt ms : ℝ) := by exact_mod_cast h.1
    simp only [iff_true]
    linarith
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq, Bool.not_false] at h
    have := withinAll_hi e.trees ms h.2 hx
    have h' : (e.base : ℝ) + (sumInt ms : ℝ) < ((e.τ : Int) : ℝ) := by exact_mod_cast h.1
    simp only [Bool.false_eq_true, iff_false, not_le]
    linarith

theorem monoCut_sound (j : ℕ) (up : Bool) (T : Tree) (cs : Cuts) (h : T.monoCut B j up cs = true)
    {x x' : ℕ → ℝ} (hx : B.Mem x) (hx' : B.Mem x') (hr : Raised j x x') :
    Ordered up (T.eval x) (T.eval x') := by
  induction T generalizing cs with
  | leaf v => cases up <;> simp [Ordered, Tree.eval]
  | node f t l r ihl ihr =>
    cases cs with
    | none => simp [Tree.monoCut] at h
    | cut c cl cr =>
    simp only [Tree.monoCut, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hl, hr'⟩, hsplit⟩ := h
    unfold Tree.eval
    by_cases h1 : x f ≤ t <;> by_cases h2 : x' f ≤ t
    · rw [if_pos h1, if_pos h2]
      exact ihl cl (by simpa [lowOk_of_mem hx h1] using hl)
    · -- x goes low, x' goes high: the split is on `j`, and the cut separates the two sides
      rw [if_pos h1, if_neg h2]
      have h2' : (t : ℝ) < x' f := lt_of_not_ge h2
      have hfj : f = j := by
        by_contra hne
        exact h2 (hr.1 f hne ▸ h1)
      subst hfj
      have hlo := lowOk_of_mem hx h1
      have hhi := highOk_of_mem hx' h2'
      simp only [hlo, hhi, Bool.not_true, Bool.false_eq_true, or_false, false_or] at hsplit
      rcases hsplit with hne | hsplit
      · simp [Nat.beq_refl] at hne
      cases up
      · simp only [Bool.false_eq_true, if_false, Bool.and_eq_true] at hsplit
        simp only [Ordered, Bool.false_eq_true, if_false]
        linarith [allGe_sound l hsplit.1 hx, allLe_sound r hsplit.2 hx']
      · simp only [if_true, Bool.and_eq_true] at hsplit
        simp only [Ordered, if_true]
        linarith [allLe_sound l hsplit.1 hx, allGe_sound r hsplit.2 hx']
    · -- x goes high, x' goes low: impossible
      exfalso
      by_cases hfj : f = j
      · subst hfj; exact h1 (hr.2.trans h2)
      · exact h1 (hr.1 f hfj ▸ h2)
    · rw [if_neg h1, if_neg h2]
      exact ihr cr (by simpa [highOk_of_mem hx (lt_of_not_ge h1)] using hr')

/-- **Monotonicity.** If the monotonicity certificate is accepted, the ensemble's score is
monotone in feature `j` (increasing if `up`) between any two inputs of the box that differ only
in `j`. -/
theorem monotoneCert_sound (e : Ensemble) (j : ℕ) (up : Bool) (cs : List Cuts) (B : Box)
    (h : monotoneCert j up e.trees cs B = true) {x x' : ℕ → ℝ} (hx : B.Mem x) (hx' : B.Mem x')
    (hr : Raised j x x') : Ordered up (e.score x) (e.score x') := by
  have key : ∀ (ts : List Tree) (cs : List Cuts), monotoneCert j up ts cs B = true →
      Ordered up (ts.map fun t => t.eval x).sum (ts.map fun t => t.eval x').sum := by
    intro ts
    induction ts with
    | nil => intro cs _; cases up <;> simp [Ordered]
    | cons t ts ih =>
      intro cs h
      cases cs with
      | nil => simp [monotoneCert] at h
      | cons c cs =>
        simp only [monotoneCert, Bool.and_eq_true] at h
        have h1 := monoCut_sound j up t c h.1 hx hx' hr
        have h2 := ih cs h.2
        cases up <;> simp only [Ordered, Bool.false_eq_true, if_false, if_true, List.map_cons,
          List.sum_cons] at h1 h2 ⊢ <;> linarith
  have := key e.trees cs h
  unfold Ensemble.score
  cases up <;> simp only [Ordered, Bool.false_eq_true, if_false, if_true] at this ⊢ <;> linarith

end OpenTheory.Checks.Tree
