import Specs.MLPExact
import Specs.Linear
import Properties.Linear

/-!
# The packed linear robustness check is sound

`Checks.Linear.robustPacked` decides robustness of a linear model on a box with about twenty
big-integer operations, whatever the number of features. The model and the box are those the
certificate stores (`packedModel`, `packedBox`): weight `f` is `slot f Wp − slot f Wm`, bounds `f`
are `slot (d − 1 − f) LR − O` and `slot (d − 1 − f) HR − O`. `robustPacked_sound`: an accepted check
means the stored model decides `c` on every real input of the stored box; `linearRobustPacked_sound`
states it as `Sound` with `δ = 0` for the card `robust-decision`.
-/

open Finset OpenTheory.Slots MeasureTheory

namespace OpenTheory.Checks.Linear

open OpenTheory.Checks.Tree (Bound Box intLe intLt intLe_eq intLt_eq)

/-- The linear model a packed certificate stores. -/
def packedModel (B d : ℕ) (bias τ : ℤ) (Wp Wm : ℕ) : LinearModel :=
  ⟨bias, τ, (List.range d).map fun f => (slot B f Wp : ℤ) - slot B f Wm⟩

/-- The box a packed certificate stores (bounds reversed and shifted by `O`). -/
def packedBox (B d O LR HR : ℕ) : Box :=
  (List.range d).map fun f => ⟨some ((slot B (d - 1 - f) LR : ℤ) - O), some ((slot B (d - 1 - f) HR : ℤ) - O)⟩

theorem scoreFrom_range (g : ℕ → ℤ) (x : ℕ → ℝ) :
    ∀ (d f : ℕ), scoreFrom ((List.range d).map g) f x = ∑ i ∈ range d, (g i : ℝ) * x (f + i)
  | 0, f => by simp [scoreFrom]
  | d + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, scoreFrom,
      scoreFrom_range (g ∘ Nat.succ) x d (f + 1), Finset.sum_range_succ']
    simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by rw [show f + 1 + i = f + (i + 1) by ring]

theorem box_get (L : Box) (f : ℕ) : L.get f = L.getD f {} := by
  induction L generalizing f with
  | nil => rfl
  | cons b L ih => cases f <;> simp [Box.get, ih]

theorem dotSlot_spec (B d P : ℕ) : dotSlot B d P = P / 2 ^ (B * (d - 1)) % 2 ^ B := by
  simp only [dotSlot, MLP.pow2_eq, Nat.mul_eq, Nat.sub_eq]
  rw [← Nat.shiftRight_eq_div_pow]; rfl

/-- Slot `d − 1` of a product of packed vectors (the second reversed) is their dot product. -/
theorem dotSlot_eq {B d mA mC A C : ℕ} (hA : A < 2 ^ (B * d)) (hAd : ∀ j, slot B j A < 2 ^ mA)
    (hC : C < 2 ^ (B * d)) (hCd : ∀ j, slot B j C < 2 ^ mC) (hX : d * 2 ^ (mA + mC) < 2 ^ B) :
    dotSlot B d (A * C) = ∑ f ∈ range d, slot B f A * slot B (d - 1 - f) C := by
  set cA := Kronecker.slots B d A
  set xC := (Kronecker.slots B d C).reverse
  have hlen : cA.length = xC.length := by simp [cA, xC, Kronecker.length_slots]
  have hx : ∀ y ∈ xC, y ≤ 2 ^ mC - 1 := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
    exact Nat.le_sub_one_of_lt (hCd k)
  have hsum : cA.sum ≤ d * (2 ^ mA - 1) := by
    have := List.sum_le_length_nsmul cA (2 ^ mA - 1) (by
      intro y hy; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy; exact Nat.le_sub_one_of_lt (hAd k))
    simpa [cA, Kronecker.length_slots] using this
  have hB : cA.sum * (2 ^ mC - 1) < 2 ^ B := by
    calc cA.sum * (2 ^ mC - 1) ≤ d * (2 ^ mA - 1) * (2 ^ mC - 1) := Nat.mul_le_mul_right _ hsum
      _ ≤ d * 2 ^ (mA + mC) := by
        rw [pow_add, Nat.mul_assoc]; exact Nat.mul_le_mul_left d (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ < 2 ^ B := hX
  have hk := Kronecker.kronecker_dot cA xC hlen hx hB
  rw [List.reverse_reverse, Kronecker.pack_slots hA, Kronecker.pack_slots hC] at hk
  have hxl : xC.length = d := by simp [xC, Kronecker.length_slots]
  rw [hxl, ← pow_mul] at hk
  rw [dotSlot_spec, hk]
  have ecA : cA = (List.range d).map fun f => slot B f A := rfl
  have exC : xC = (List.range d).map fun f => slot B (d - 1 - f) C := by
    apply List.ext_getElem (by simp [xC, Kronecker.length_slots])
    intro i h1 h2
    simp only [xC, Kronecker.slots, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    rfl
  rw [ecA, exC, MLP.zipWith_range, MLP.sum_range_list']

/-- The digit sum of a packed vector whose digits sum below `2^B − 1`. -/
theorem mod_pred_eq_sum {B d m A : ℕ} (hA : A < 2 ^ (B * d)) (hAd : ∀ j, slot B j A < 2 ^ m)
    (hX : d * 2 ^ m < 2 ^ B - 1) : A % (2 ^ B - 1) = ∑ f ∈ range d, slot B f A := by
  have hsum : (Kronecker.slots B d A).sum ≤ d * (2 ^ m - 1) := by
    have := List.sum_le_length_nsmul (Kronecker.slots B d A) (2 ^ m - 1) (by
      intro y hy; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy; exact Nat.le_sub_one_of_lt (hAd k))
    simpa [Kronecker.length_slots] using this
  have hlt : (Kronecker.slots B d A).sum < 2 ^ B - 1 :=
    lt_of_le_of_lt (le_trans hsum (Nat.mul_le_mul_left d (Nat.sub_le _ _))) hX
  nth_rewrite 1 [← Kronecker.pack_slots (B := B) hA]
  rw [pack_mod_pred, Nat.mod_eq_of_lt hlt, Kronecker.slots, MLP.sum_range_list']
  rfl

/-- **Packed robustness.** If `robustPacked` accepts `c`, the model the certificate stores decides
`c` on every real input of the box it stores. -/
theorem robustPacked_sound {B d mW mL O : ℕ} {bias τ : ℤ} {Wp Wm LR HR : ℕ} {c : Bool}
    (h : robustPacked B d mW mL O bias τ Wp Wm LR HR c = true) (x : ℕ → ℝ)
    (hx : (packedBox B d O LR HR).Mem x) :
    ((packedModel B d bias τ Wp Wm).Approves x ↔ c = true) := by
  simp only [robustPacked, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, MLP.pow2_eq, Nat.mul_eq,
    Nat.add_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hd, hWp⟩, hWm⟩, hLR⟩, hHR⟩, hX⟩, hc⟩ := h
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; simp at hX
    · exact h0
  obtain ⟨Wplt, Wpd⟩ := MLP.digitsBelow_spec hB0 hWp
  obtain ⟨Wmlt, Wmd⟩ := MLP.digitsBelow_spec hB0 hWm
  obtain ⟨LRlt, LRd⟩ := MLP.digitsBelow_spec hB0 hLR
  obtain ⟨HRlt, HRd⟩ := MLP.digitsBelow_spec hB0 hHR
  have hX' : d * 2 ^ (mW + mL) < 2 ^ B := lt_of_lt_of_le hX (Nat.sub_le _ _)
  have hXW : d * 2 ^ mW < 2 ^ B - 1 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by norm_num) (by omega))) hX
  -- the four dot products and the two weight sums
  have kpl := dotSlot_eq Wplt Wpd LRlt LRd hX'
  have kmh := dotSlot_eq Wmlt Wmd HRlt HRd hX'
  have kph := dotSlot_eq Wplt Wpd HRlt HRd hX'
  have kml := dotSlot_eq Wmlt Wmd LRlt LRd hX'
  have sp := mod_pred_eq_sum Wplt Wpd hXW
  have sm := mod_pred_eq_sum Wmlt Wmd hXW
  -- the score, term by term against the corners
  set lo := fun f => ((slot B (d - 1 - f) LR : ℤ) - O)
  set hi := fun f => ((slot B (d - 1 - f) HR : ℤ) - O)
  have hbox : ∀ f < d, (lo f : ℝ) ≤ x f ∧ x f ≤ hi f := by
    intro f hf
    have := hx f
    rw [box_get, packedBox, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hf] at this
    simp only [Option.map_some, Option.getD_some] at this
    exact ⟨this.1 _ rfl, this.2 _ rfl⟩
  have hscore : (packedModel B d bias τ Wp Wm).score x =
      bias + ∑ f ∈ range d, (((slot B f Wp : ℤ) - slot B f Wm : ℤ) : ℝ) * x f := by
    simp only [LinearModel.score, packedModel, scoreFrom_range, Nat.zero_add]
  have lower : (∑ f ∈ range d, ((slot B f Wp : ℝ) * lo f - (slot B f Wm : ℝ) * hi f)) ≤
      ∑ f ∈ range d, (((slot B f Wp : ℤ) - slot B f Wm : ℤ) : ℝ) * x f := by
    refine Finset.sum_le_sum fun f hf => ?_
    have ⟨h1, h2⟩ := hbox f (Finset.mem_range.mp hf)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (slot B f Wp), Nat.cast_nonneg (α := ℝ) (slot B f Wm)]
  have upper : (∑ f ∈ range d, (((slot B f Wp : ℤ) - slot B f Wm : ℤ) : ℝ) * x f) ≤
      ∑ f ∈ range d, ((slot B f Wp : ℝ) * hi f - (slot B f Wm : ℝ) * lo f) := by
    refine Finset.sum_le_sum fun f hf => ?_
    have ⟨h1, h2⟩ := hbox f (Finset.mem_range.mp hf)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (slot B f Wp), Nat.cast_nonneg (α := ℝ) (slot B f Wm)]
  -- the corner sums are the packed quantities
  have expand : ∀ (P Q : ℕ → ℕ) (b : ℕ → ℤ),
      (∑ f ∈ range d, ((P f : ℝ) * ((Q f : ℤ) - O : ℤ))) =
        (∑ f ∈ range d, (P f * Q f : ℕ) : ℝ) - O * (∑ f ∈ range d, (P f : ℕ) : ℝ) := by
    intro P Q _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => by push_cast; ring
  have eLow : (∑ f ∈ range d, ((slot B f Wp : ℝ) * lo f - (slot B f Wm : ℝ) * hi f)) =
      ((dotSlot B d (Wp * LR) : ℕ) : ℝ) - O * (Wp % (2 ^ B - 1) : ℕ) -
        (((dotSlot B d (Wm * HR) : ℕ) : ℝ) - O * (Wm % (2 ^ B - 1) : ℕ)) := by
    rw [Finset.sum_sub_distrib, expand _ _ lo, expand _ _ hi, kpl, kmh, sp, sm]
    push_cast; ring
  have eUp : (∑ f ∈ range d, ((slot B f Wp : ℝ) * hi f - (slot B f Wm : ℝ) * lo f)) =
      ((dotSlot B d (Wp * HR) : ℕ) : ℝ) - O * (Wp % (2 ^ B - 1) : ℕ) -
        (((dotSlot B d (Wm * LR) : ℕ) : ℝ) - O * (Wm % (2 ^ B - 1) : ℕ)) := by
    rw [Finset.sum_sub_distrib, expand _ _ hi, expand _ _ lo, kph, kml, sp, sm]
    push_cast; ring
  unfold LinearModel.Approves
  rw [hscore]
  cases c with
  | true =>
    simp only [Bool.cond_true, intLe_eq, decide_eq_true_eq, Int.add_def, Int.ofNat_eq_natCast] at hc
    rw [show Wp.mod (2 ^ B - 1) = Wp % (2 ^ B - 1) from rfl, show Wm.mod (2 ^ B - 1) = Wm % (2 ^ B - 1) from rfl] at hc
    generalize Wp % (2 ^ B - 1) = σp at hc eLow
    generalize Wm % (2 ^ B - 1) = σm at hc eLow
    have hc' := (Int.cast_le (R := ℝ)).mpr hc
    simp only [iff_true, packedModel]
    push_cast at hc' eLow lower ⊢
    linarith
  | false =>
    simp only [Bool.cond_false, intLt_eq, decide_eq_true_eq, Int.add_def, Int.ofNat_eq_natCast] at hc
    rw [show Wp.mod (2 ^ B - 1) = Wp % (2 ^ B - 1) from rfl, show Wm.mod (2 ^ B - 1) = Wm % (2 ^ B - 1) from rfl] at hc
    generalize Wp % (2 ^ B - 1) = σp at hc eUp
    generalize Wm % (2 ^ B - 1) = σm at hc eUp
    have hc' := (Int.cast_lt (R := ℝ)).mpr hc
    simp only [Bool.false_eq_true, iff_false, not_le, packedModel]
    push_cast at hc' eUp upper ⊢
    linarith

/-- A packed robustness certificate: the numbers `robustPackedN` reads. -/
structure PackedCert where
  B : ℕ
  d : ℕ
  mW : ℕ
  mL : ℕ
  O : ℕ
  zb : ℕ
  zt : ℕ
  Wp : ℕ
  Wm : ℕ
  LR : ℕ
  HR : ℕ
  c : ℕ

/-- **`robust-decision`** (linear models, packed). For every certificate the kernel accepts, the
model it stores decides `c` on every real input of the box it stores. -/
theorem linearRobustPacked_sound :
    Sound (Measure.dirac ())
      (fun _ (θ : PackedCert) => robustPackedN θ.B θ.d θ.mW θ.mL θ.O θ.zb θ.zt θ.Wp θ.Wm θ.LR θ.HR θ.c = true)
      (fun θ => (⟨.property (Decides (Nat.beq θ.c 1)), .region {x | (packedBox θ.B θ.d θ.O θ.LR θ.HR).Mem x}, .all⟩ :
        Spec LinearModel (ℕ → ℝ)).Target (packedModel θ.B θ.d (Tree.zig θ.zb) (Tree.zig θ.zt) θ.Wp θ.Wm)) 0 := by
  rw [sound_exact_iff]
  rintro θ h x hx
  simp only [robustPackedN, Bool.and_eq_true] at h
  exact robustPacked_sound h.2 x hx

end OpenTheory.Checks.Linear
