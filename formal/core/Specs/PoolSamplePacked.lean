import Specs.MLPExact
import Specs.PoolSample

/-!
# The packed sample check is the claim types' acceptance

`Checks.poolSamplePacked` (exact tail) and `Checks.poolSamplePackedW` (Chernoff witness) check a
beacon sample with a fixed number of big-integer operations, whatever its size. The request stores
the `n` positions as slots: blocks `Bk`, quotients `Q` and indices `J` in base `2^S`, the items'
two numbers `A` and `C` in base `2^T`. `decodeDrawn` reads them back as the list of positions that
`pool-sample` takes, and the two facts outside the kernel are stated about that list, exactly as
before (`Faithful`: the blocks are the seed's, the numbers are the committed items').

* `index_of_indicesPacked`: slot `i` of `J` is slot `i` of `Bk` modulo `N`;
* `slot_differ`: slot `i` of `differ` is `1` exactly when `aᵢ ≠ cᵢ`;
* `card_counted`: `countPacked` is the number of sampled items with the counted outcome;
* `claim_of_poolSamplePacked`, `claim_of_poolSamplePackedW`: an accepted check, on a faithful
  request, is `PoolRate.Claim` for the derived sample, the acceptance of `ClaimTypes.poolRate`;
* `poolRate_accepts_packed`: the same for the procedure `exact-match` (`s = 0`);
* `PoolRate.Claim.of_poolPacked(W)`: the bit-count check on bits given one per slot (`pool-packed`)
  is a `PoolRate.Claim` for those bits;
* `rateGap_of_claims`: four such claims, the counted outcome and its complement on each of two
  pools, are the acceptance of `ClaimTypes.rateGap` and `rateRatio`.
-/

open Finset OpenTheory.Slots OpenTheory.Checks OpenTheory.DesignSampling

namespace OpenTheory.PoolSample

/-- The positions a packed request stores. -/
def decodeDrawn (n S T Bk J A C : ℕ) : List Drawn :=
  (List.range n).map fun i => ⟨slot S i Bk, slot S i J, slot T i A, slot T i C⟩

@[simp] theorem length_decodeDrawn (n S T Bk J A C : ℕ) : (decodeDrawn n S T Bk J A C).length = n := by
  simp [decodeDrawn]

/-- `K·P + Q` slot by slot, when no slot overflows. -/
theorem slot_mul_add {s m K P Q : ℕ} (hP : P < 2 ^ (s * m)) (hQ : Q < 2 ^ (s * m))
    (h : ∀ j < m, K * slot s j P + slot s j Q < 2 ^ s) (j : ℕ) :
    slot s j (K * P + Q) = K * slot s j P + slot s j Q := by
  have e : K * P + Q = Kronecker.pack s ((List.range m).map fun c => K * slot s c P + slot s c Q) := by
    rw [Kronecker.pack, ofDigits_range_map]
    conv_lhs => rw [eq_sum_slots hP, eq_sum_slots hQ]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e, slot_pack (fun y hy => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact h c (List.mem_range.mp hc))]
  by_cases hj : j < m
  · simp [List.getD_eq_getElem?_getD, hj]
  · have hle : 2 ^ (s * m) ≤ 2 ^ (s * j) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left s (not_lt.mp hj))
    rw [slot_of_lt (lt_of_lt_of_le hP hle), slot_of_lt (lt_of_lt_of_le hQ hle)]
    simp [List.getD_eq_getElem?_getD, hj]

/-- The top bit of each of `n` slots, as `0` or `1` in the slot. -/
theorem slot_signs {s n v : ℕ} (hs : 0 < s) (j : ℕ) :
    slot s j (Nat.land (Nat.shiftRight v (Nat.sub s 1)) (MLP.ones s n)) =
      if j < n ∧ 2 ^ (s - 1) ≤ slot s j v then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight v (Nat.sub s 1)) (MLP.ones s n) = (v >>> (s - 1)) &&& MLP.ones s n := rfl
  rw [e, slot_land, MLP.ones_eq, slot_ones hs]
  have hbit : slot s j (v >>> (s - 1)) % 2 = if 2 ^ (s - 1) ≤ slot s j v then 1 else 0 := by
    have h0 := testBit_slot s j (v >>> (s - 1)) 0
    rw [Nat.testBit_zero, Nat.testBit_shiftRight] at h0
    have h1 := testBit_slot s j v (s - 1)
    rw [MLP.testBit_sign hs (slot_lt _ _ _)] at h1
    simp only [hs, decide_true, Bool.true_and, Nat.add_zero] at h0
    simp only [show s - 1 < s by omega, decide_true, Bool.true_and] at h1
    rw [show s - 1 + s * j = s * j + (s - 1) by ring, ← h1] at h0
    rcases Nat.mod_two_eq_zero_or_one (slot s j (v >>> (s - 1))) with h | h <;>
      simp only [h] at h0 ⊢ <;> split <;> simp_all
  by_cases hj : j < n
  · rw [if_pos hj, Nat.and_one_is_mod, hbit]; simp [hj]
  · rw [if_neg hj, Nat.and_zero]; simp [hj]

/-- **The indices.** Slot `i` of `J` is slot `i` of `Bk` modulo `N`. -/
theorem index_of_indicesPacked {N n S mQ mJ Bk Q J : ℕ} (h : indicesPacked N n S mQ mJ Bk Q J = true)
    {i : ℕ} (hi : i < n) : slot S i J = slot S i Bk % N := by
  simp only [indicesPacked, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, MLP.pow2_eq,
    Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hN, hmJ⟩, hQ⟩, hJ⟩, hfit⟩, hB⟩, hNJ⟩, hG⟩ := h
  have hS : 0 < S := by omega
  obtain ⟨Qlt, Qd⟩ := MLP.digitsBelow_spec hS hQ
  obtain ⟨Jlt, Jd⟩ := MLP.digitsBelow_spec hS hJ
  obtain ⟨-, Gd⟩ := MLP.digitsBelow_spec hS hG
  have hones : ∀ j, slot S j (MLP.ones S n) = if j < n then 1 else 0 := fun j => by
    rw [MLP.ones_eq, slot_ones hS]
  have h2 : 2 ^ mJ + 2 ^ mJ ≤ 2 ^ S := by
    rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hmJ
  -- the offset slots `2^mJ − N + jᵢ` are below `2^mJ`
  have sG := slot_mul_add (K := 2 ^ mJ - N) (MLP.ones_lt hS n) Jlt (fun j hj => by
    rw [hones, if_pos hj, Nat.mul_one]; have := Jd j; omega) i
  have hji : slot S i J < N := by
    have := Gd i; rw [sG, hones, if_pos hi, Nat.mul_one] at this; omega
  -- `Bk = N·Q + J` slot by slot
  have sB := slot_mul_add (K := N) Qlt Jlt (fun j _ => lt_of_lt_of_le
    (Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left (Qd j) hN) (Jd j)) hfit) i
  rw [hB, sB, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hji]

/-- **The outcomes.** Slot `j` of `differ` is `1` exactly when `j < n` and `aⱼ ≠ cⱼ`. -/
theorem slot_differ {T n A C : ℕ} (hT : 2 ≤ T) (hA : A < 2 ^ (T * n)) (hAd : ∀ j, slot T j A < 2 ^ (T - 1))
    (hC : C < 2 ^ (T * n)) (hCd : ∀ j, slot T j C < 2 ^ (T - 1)) (j : ℕ) :
    slot T j (differ T n A C) = if j < n ∧ slot T j A ≠ slot T j C then 1 else 0 := by
  have hT0 : 0 < T := by omega
  have e : differ T n A C = Nat.land (Nat.shiftRight ((2 ^ (T - 1) - 1) * MLP.ones T n + (A ^^^ C))
      (Nat.sub T 1)) (MLP.ones T n) := by
    simp only [differ, MLP.pow2_eq]; rfl
  have hT2 : 2 ^ (T - 1) + 2 ^ (T - 1) = 2 ^ T := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  have hX : ∀ j, slot T j (A ^^^ C) < 2 ^ (T - 1) := fun j => by
    rw [slot_xor]; exact Nat.xor_lt_two_pow (hAd j) (hCd j)
  have sG := slot_mul_add (K := 2 ^ (T - 1) - 1) (MLP.ones_lt hT0 n) (Nat.xor_lt_two_pow hA hC)
    (fun j hj => by
      rw [MLP.ones_eq, slot_ones hT0, if_pos hj, Nat.mul_one]; have := hX j
      have : 0 < 2 ^ (T - 1) := by positivity
      omega) j
  rw [e, slot_signs hT0, sG, MLP.ones_eq, slot_ones hT0, slot_xor]
  by_cases hj : j < n
  · simp only [hj, if_true, Nat.mul_one, true_and]
    have hp : 0 < 2 ^ (T - 1) := by positivity
    by_cases hac : slot T j A = slot T j C
    · rw [hac, Nat.xor_self]; simp
    · have : slot T j A ^^^ slot T j C ≠ 0 := fun h0 => hac (by
        have := congrArg (· ^^^ slot T j C) h0
        simpa [Nat.xor_assoc] using this)
      simp only [hac, ne_eq, not_false_eq_true, ite_true]
      rw [ite_eq_left_iff.mpr]; intro h; omega
  · simp [hj]

/-- **The count.** On a faithful request, `countPacked` is the number of sampled items whose outcome
is the counted one. -/
theorem card_counted [NeZero N] {Cm : Fin N → ℕ × ℕ} {w : ℕ} {seed : Fin n → Fin (2 ^ w)}
    {s S mQ mJ T Bk Q J A C : ℕ} (hf : Faithful Cm seed (decodeDrawn n S T Bk J A C))
    (hI : indicesPacked N n S mQ mJ Bk Q J = true) (hIt : itemsPacked T n A C = true) :
    (univ.filter fun i => decide (Counted (Nat.beq s 1) Cm (derive seed i)) = true).card =
      countPacked s T n A C := by
  simp only [itemsPacked, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, MLP.pow2_eq, Nat.mul_eq,
    Nat.sub_eq] at hIt
  obtain ⟨⟨⟨hT, hA⟩, hC⟩, hn⟩ := hIt
  have hT0 : 0 < T := by omega
  obtain ⟨Alt, Ad⟩ := MLP.digitsBelow_spec hT0 hA
  obtain ⟨Clt, Cd⟩ := MLP.digitsBelow_spec hT0 hC
  -- each position's numbers are those of the committed item it derives
  have hitem : ∀ i : Fin n, (slot T i A, slot T i C) = Cm (derive seed i) := by
    intro i
    have hi : i.val < (decodeDrawn n S T Bk J A C).length := by simp
    have hb := hf.block i hi
    have := hf.item i hi (derive seed i) (by
      simp only [decodeDrawn, List.getElem_map, List.getElem_range] at hb ⊢
      rw [index_of_indicesPacked hI i.isLt, hb]; rfl)
    simpa [decodeDrawn] using this
  have hcount : ∀ i : Fin n, (decide (Counted (Nat.beq s 1) Cm (derive seed i)) = true) ↔
      (if Nat.beq s 1 then slot T i A = slot T i C else slot T i A ≠ slot T i C) := by
    intro i; rw [decide_eq_true_iff]; unfold Counted; rw [← hitem i]
  -- the number of differing positions
  have hm : differ T n A C % (2 ^ T - 1) = (univ.filter fun i : Fin n => slot T i A ≠ slot T i C).card := by
    have hlt : differ T n A C < 2 ^ (T * n) :=
      lt_of_le_of_lt (show Nat.land _ (MLP.ones T n) ≤ MLP.ones T n from Nat.and_le_right)
        (MLP.ones_lt hT0 n)
    rw [MLP.mod_pred_eq_sum (m := 1) hlt (fun j => by
      rw [slot_differ hT Alt Ad Clt Cd]; split <;> norm_num) (by omega)]
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slot_differ hT Alt Ad Clt Cd]
    simp [i.isLt]
  have hc : countPacked s T n A C =
      cond (Nat.beq s 1) (n - differ T n A C % (2 ^ T - 1)) (differ T n A C % (2 ^ T - 1)) := by
    simp only [countPacked, MLP.pow2_eq, Nat.sub_eq]; rfl
  rw [hc, hm, Finset.filter_congr (fun i _ => hcount i)]
  cases Nat.beq s 1
  · simp
  · have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (p := fun i => slot T i A = slot T i C)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [ite_true, cond_true, ne_eq] at this ⊢
    omega

/-- **The packed sample, exact tail, is a `pool-rate` acceptance.** -/
theorem claim_of_poolSamplePacked [NeZero N] {Cm : Fin N → ℕ × ℕ} {w : ℕ} {seed : Fin n → Fin (2 ^ w)}
    {s S mQ mJ T k a b d Bk Q J A C : ℕ} (hf : Faithful Cm seed (decodeDrawn n S T Bk J A C))
    (h : poolSamplePacked N s n S mQ mJ T k a b d Bk Q J A C = true) :
    PoolRate.Claim (fun i => decide (Counted (Nat.beq s 1) Cm (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolSamplePacked, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨hI, hIt⟩, hk⟩, ht⟩ := h
  simp only [tailOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq] at ht
  obtain ⟨⟨⟨hab, hb⟩, hd⟩, ht⟩ := ht
  exact PoolRate.Claim.of_tail (by rw [card_counted hf hI hIt]; exact hk) hab hb hd
    (by rwa [PoolRate.tailFast_eq hab] at ht)

/-- **The packed sample, Chernoff witness, is a `pool-rate` acceptance.** -/
theorem claim_of_poolSamplePackedW [NeZero N] {Cm : Fin N → ℕ × ℕ} {w : ℕ} {seed : Fin n → Fin (2 ^ w)}
    {s S mQ mJ T k a b u v d Bk Q J A C : ℕ} (hf : Faithful Cm seed (decodeDrawn n S T Bk J A C))
    (h : poolSamplePackedW N s n S mQ mJ T k a b u v d Bk Q J A C = true) :
    PoolRate.Claim (fun i => decide (Counted (Nat.beq s 1) Cm (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolSamplePackedW, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨hI, hIt⟩, hk⟩, hw⟩ := h
  simp only [witnessOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq, Nat.add_eq,
    Nat.sub_eq] at hw
  obtain ⟨⟨⟨⟨⟨hab, hb⟩, hu⟩, huv⟩, hd⟩, hw⟩ := hw
  exact PoolRate.Claim.of_witness (by rw [card_counted hf hI hIt]; exact hk) hab hb hu huv hd hw

/-- The count of `n` one-bit slots is their remainder modulo `2^T − 1`. -/
theorem card_bitsPacked {T n X : ℕ} (h : bitsPacked T n X = true) :
    (univ.filter fun i : Fin n => decide (slot T i X = 1) = true).card = X % (2 ^ T - 1) := by
  simp only [bitsPacked, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, MLP.pow2_eq, Nat.mul_eq,
    Nat.sub_eq] at h
  obtain ⟨⟨hT, hX⟩, hn⟩ := h
  obtain ⟨Xlt, Xd⟩ := MLP.digitsBelow_spec (by omega) hX
  rw [MLP.mod_pred_eq_sum (m := 1) Xlt Xd (by omega), Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Xd i
  simp only [pow_one] at this
  interval_cases h : slot T i X <;> simp

end OpenTheory.PoolSample

namespace OpenTheory.PoolRate

/-- **A `true` packed bit-count check, exact tail, is a claim** about the bits it stores. -/
theorem Claim.of_poolPacked {T n k a b d X : ℕ}
    (h : poolPacked T n k a b d X = true) :
    Claim (fun i : Fin n => decide (slot T i X = 1)) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolPacked, Bool.and_eq_true, Nat.ble_eq, MLP.pow2_eq, Nat.sub_eq] at h
  obtain ⟨⟨hB, hk⟩, ht⟩ := h
  simp only [tailOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq] at ht
  obtain ⟨⟨⟨hab, hb⟩, hd⟩, ht⟩ := ht
  exact Claim.of_tail (by rw [PoolSample.card_bitsPacked hB]; exact hk) hab hb hd
    (by rwa [tailFast_eq hab] at ht)

/-- **A `true` packed bit-count check, Chernoff witness, is a claim** about the bits it stores. -/
theorem Claim.of_poolPackedW {T n k a b u v d X : ℕ}
    (h : poolPackedW T n k a b u v d X = true) :
    Claim (fun i : Fin n => decide (slot T i X = 1)) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolPackedW, Bool.and_eq_true, Nat.ble_eq, MLP.pow2_eq, Nat.sub_eq] at h
  obtain ⟨⟨hB, hk⟩, hw⟩ := h
  simp only [witnessOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq, Nat.add_eq,
    Nat.sub_eq] at hw
  obtain ⟨⟨⟨⟨⟨hab, hb⟩, hu⟩, huv⟩, hd⟩, hw⟩ := hw
  exact Claim.of_witness (by rw [PoolSample.card_bitsPacked hB]; exact hk) hab hb hu huv hd hw

end OpenTheory.PoolRate

namespace OpenTheory.PoolSample

/-- **The kernel's packed check is `ClaimTypes.poolRate`'s acceptance** (procedure `exact-match`:
an item fails when its output differs from its label, `s = 0`), exact tail or Chernoff witness. -/
theorem poolRate_accepts_packed [NeZero N] {Cm : Fin N → ℕ × ℕ} {w : ℕ} {seed : Fin n → Fin (2 ^ w)}
    {S mQ mJ T k a b d Bk Q J A C : ℕ} (hf : Faithful Cm seed (decodeDrawn n S T Bk J A C))
    (h : poolSamplePacked N 0 n S mQ mJ T k a b d Bk Q J A C = true ∨
      ∃ u v, poolSamplePackedW N 0 n S mQ mJ T k a b u v d Bk Q J A C = true) :
    PoolRate.Claim (fun i => decide (Counted false Cm (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  rcases h with h | ⟨u, v, h⟩
  · exact claim_of_poolSamplePacked hf h
  · exact claim_of_poolSamplePackedW hf h

/-- **Four claims are a `rate-gap` acceptance**: the counted outcome (`s = 1`) and its complement
(`s = 0`) on pool `A`'s sample (the seed's first `nA` blocks) and on pool `B`'s (the next `nB`),
each given by `claim_of_poolSamplePacked` or `claim_of_poolSamplePackedW`. -/
theorem rateGap_of_claims {NA NB nA nB w : ℕ} [NeZero NA] [NeZero NB]
    {CA : Fin NA → ℕ × ℕ} {CB : Fin NB → ℕ × ℕ} {s : Fin (nA + nB) → Fin (2 ^ w)}
    {kA kA' kB kB' : ℕ} {pA qA pB qB δA δA' δB δB' : ℝ}
    (c1 : PoolRate.Claim (fun i => decide (Counted (Nat.beq 1 1) CA (derive (RateGap.seedA s) i))) kA pA δA)
    (c2 : PoolRate.Claim (fun i => decide (Counted (Nat.beq 0 1) CA (derive (RateGap.seedA s) i))) kA' qA δA')
    (c3 : PoolRate.Claim (fun i => decide (Counted (Nat.beq 1 1) CB (derive (RateGap.seedB s) i))) kB pB δB)
    (c4 : PoolRate.Claim (fun i => decide (Counted (Nat.beq 0 1) CB (derive (RateGap.seedB s) i))) kB' qB δB') :
    RateGap.Claim (Counted true CA) (Counted true CB) s ⟨kA, kA', kB, kB', pA, qA, pB, qB⟩ δA δA' δB δB' := by
  have neg : ∀ {M : ℕ} (C : Fin M → ℕ × ℕ) (j : Fin M),
      decide (¬ Counted true C j) = decide (Counted false C j) := by
    intro M C j; simp [Counted]
  refine ⟨c1, ?_, c3, ?_⟩
  · simpa only [neg, show Nat.beq 0 1 = false from rfl] using c2
  · simpa only [neg, show Nat.beq 0 1 = false from rfl] using c4

end OpenTheory.PoolSample
