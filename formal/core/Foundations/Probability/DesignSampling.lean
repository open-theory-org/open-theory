import Foundations.Probability.BinomialTail
import Mathlib.Probability.Distributions.Uniform

/-!
# Design-based sampling from a public seed

A certifier commits to a pool of `N` items and to a property `e` of each item, for example
"the deployed model's logged answer to this item is wrong". After both commitments, a public
seed is drawn and expanded into `n` blocks of `b` bits; block `i` selects pool index
`seedᵢ mod N`.

The randomness is the seed's, not nature's: nothing is assumed about how the pool arose, and
the claim is about the pool itself. The one modelling step is that the expanded seed is uniform
on `(Fin (2 ^ b))ⁿ` (random-oracle model of the beacon expansion).

* `rate_sound`: whatever count `k` and bound `p` the certifier reads off the realized sample,
  the claim `poolRate e ≤ p` fails on at most a `(1 + N/2^b)ⁿ · δ` fraction of seeds, provided
  `P(Bin(n, p) ≤ k) ≤ δ`.
* `selective_sound`: the same for an issuer who commits `M` properties (models, graders) before
  the seed and then publishes whichever certificate it likes. The total is `(1 + N/2^b)ⁿ · Σ δⱼ`.

`(1 + N/2^b)ⁿ` is the cost of reducing modulo `N`. For `b = 256` and `n, N < 2⁶⁴` it is below
`1 + 2⁻¹²⁷`. That `e` is a fixed function, not a function of the seed, is the commitment order.

References: commit-then-sample [@luck2026certified]; public randomness in election audits
[@lindeman2012gentle].
-/

noncomputable section
open Finset OpenTheory.BinomialTail
open scoped Classical

namespace OpenTheory.DesignSampling

variable {N n b : ℕ}

/-- Pool index selected by one `b`-bit block. -/
def deriveIndex [NeZero N] (v : Fin (2 ^ b)) : Fin N :=
  ⟨v.val % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- The `n` sampled pool indices. -/
def derive [NeZero N] (seed : Fin n → Fin (2 ^ b)) : Fin n → Fin N :=
  fun i => deriveIndex (seed i)

/-- Fraction of the pool with property `e`. -/
def poolRate (e : Fin N → Prop) : ℝ := ((univ.filter e).card : ℝ) / N

/-- Number of sampled positions whose item has property `e`. -/
def sampledCount (e : Fin N → Prop) (idx : Fin n → Fin N) : ℕ :=
  (univ.filter fun i => e (idx i)).card

/-- Fraction of seeds in `S`. -/
def seedFrac (S : Set (Fin n → Fin (2 ^ b))) : ℝ :=
  ((univ.filter (· ∈ S)).card : ℝ) / (2 ^ b : ℝ) ^ n

/-- Seeds on which some claim `poolRate e ≤ p` with a valid tail `P(Bin(n,p) ≤ k) ≤ δ` and at
most `k` observed hits is wrong. -/
def bad [NeZero N] (e : Fin N → Prop) (δ : ℝ) : Set (Fin n → Fin (2 ^ b)) :=
  {seed | ∃ (k : ℕ) (p : ℝ), sampledCount e (derive seed) ≤ k ∧ 0 ≤ p ∧
    binomCdf n k p ≤ δ ∧ p < poolRate e}

theorem poolRate_mem_Icc (e : Fin N → Prop) : poolRate e ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by unfold poolRate; positivity, div_le_one_of_le₀ ?_ (Nat.cast_nonneg N)⟩
  exact_mod_cast (card_filter_le _ _).trans (card_fin N).le

/-! ### Reduction modulo `N` -/

/-- At most `2^b / N + 1` blocks select a given index. -/
theorem card_deriveIndex_fiber_le [NeZero N] (j : Fin N) :
    (univ.filter fun v : Fin (2 ^ b) => deriveIndex v = j).card ≤ 2 ^ b / N + 1 := by
  have hmaps : ∀ v ∈ univ.filter (fun v : Fin (2 ^ b) => deriveIndex v = j),
      v.val / N ∈ range (2 ^ b / N + 1) := fun v _ =>
    mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right v.isLt.le))
  have hinj : Set.InjOn (fun v : Fin (2 ^ b) => v.val / N)
      ↑(univ.filter fun v : Fin (2 ^ b) => deriveIndex v = j) := by
    intro v hv w hw hvw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, deriveIndex, Fin.ext_iff] at hv hw
    exact Fin.ext (by rw [← Nat.div_add_mod v.val N, ← Nat.div_add_mod w.val N, hv, hw]; simp_all)
  simpa using card_le_card_of_injOn _ hmaps hinj

/-- Seeds mapping into a set `A` of index tuples: at most `|A| · (2^b / N + 1)ⁿ`. -/
theorem card_derive_preimage_le [NeZero N] (A : Finset (Fin n → Fin N)) :
    (univ.filter fun seed : Fin n → Fin (2 ^ b) => derive seed ∈ A).card ≤
      A.card * (2 ^ b / N + 1) ^ n := by
  rw [card_eq_sum_card_fiberwise (f := derive) (t := A)
    (s := univ.filter fun seed : Fin n → Fin (2 ^ b) => derive seed ∈ A)
    fun seed hs => by simpa using hs]
  refine (sum_le_sum fun idx _ => ?_).trans_eq (by rw [sum_const, smul_eq_mul])
  calc (filter (fun seed => derive seed = idx)
          (univ.filter fun seed : Fin n → Fin (2 ^ b) => derive seed ∈ A)).card
      ≤ (Fintype.piFinset fun i => univ.filter fun v : Fin (2 ^ b) => deriveIndex v = idx i).card :=
        card_le_card fun seed hs => Fintype.mem_piFinset.2 fun i => mem_filter.2
          ⟨mem_univ _, congrFun (mem_filter.1 hs).2 i⟩
    _ = ∏ i, (univ.filter fun v : Fin (2 ^ b) => deriveIndex v = idx i).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin n, (2 ^ b / N + 1) := prod_le_prod fun i _ => card_deriveIndex_fiber_le _
    _ = (2 ^ b / N + 1) ^ n := by simp

/-! ### Uniform indices: the exact binomial law -/

/-- The uniform law on the pool. -/
def uniformPool (N : ℕ) [NeZero N] : MeasureTheory.Measure (Fin N) :=
  (PMF.uniformOfFintype (Fin N)).toMeasure

instance [NeZero N] : MeasureTheory.IsProbabilityMeasure (uniformPool N) := by
  unfold uniformPool; infer_instance

theorem uniformPool_real [NeZero N] (e : Fin N → Prop) :
    (uniformPool N).real {j | e j} = poolRate e := by
  rw [MeasureTheory.measureReal_def, uniformPool,
    PMF.toMeasure_uniformOfFintype_apply _ (MeasurableSet.of_discrete), Fintype.card_fin,
    Fintype.card_ofFinset, ENNReal.toReal_div]
  simp [poolRate]

/-- `n` uniform indices give each tuple probability `1/Nⁿ`. -/
theorem sampleLaw_uniformPool [NeZero N] (A : Finset (Fin n → Fin N)) :
    StatLean.StatisticalLearning.sampleLaw (uniformPool N) n ↑A = A.card / (N : ENNReal) ^ n := by
  rw [← MeasureTheory.sum_measure_singleton]
  have hone : ∀ j : Fin N, uniformPool N {j} = (N : ENNReal)⁻¹ := fun j => by
    rw [uniformPool, PMF.toMeasure_uniformOfFintype_apply _ (MeasurableSet.of_discrete)]
    simp
  simp only [StatLean.StatisticalLearning.sampleLaw, MeasureTheory.Measure.pi_singleton, hone,
    prod_const, card_univ, Fintype.card_fin, sum_const, nsmul_eq_mul, ENNReal.inv_pow,
    div_eq_mul_inv]

/-- With truly uniform indices, `P(F_R(K) ≤ δ) ≤ δ` (Clopper–Pearson). -/
theorem card_clopperPearson_le [NeZero N] (e : Fin N → Prop) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((univ.filter fun idx : Fin n → Fin N =>
        binomCdf n (sampledCount e idx) (poolRate e) ≤ δ).card : ℝ) / (N : ℝ) ^ n ≤ δ := by
  set A := univ.filter fun idx : Fin n → Fin N => binomCdf n (sampledCount e idx) (poolRate e) ≤ δ
  have hset : (↑A : Set (Fin n → Fin N)) =
      {s | binomCdf n (count {j | e j} s) ((uniformPool N).real {j | e j}) ≤ δ} := by
    ext s
    simp only [A, coe_filter, mem_univ, true_and, uniformPool_real]
    exact Iff.rfl
  have h := count_clopperPearson (D := uniformPool N) (n := n)
    (MeasurableSet.of_discrete : MeasurableSet {j | e j}) δ
  rw [← hset, sampleLaw_uniformPool] at h
  have hN : (0 : ℝ) < (N : ℝ) ^ n := pow_pos (by exact_mod_cast NeZero.pos N) n
  rw [← ENNReal.ofReal_toReal (a := (A.card : ENNReal) / (N : ENNReal) ^ n)
    (ENNReal.div_ne_top (by simp) (by simp [NeZero.ne N])),
    ENNReal.ofReal_le_ofReal_iff hδ, ENNReal.toReal_div] at h
  simpa using h

/-! ### Soundness -/

/-- Bad seeds map into the Clopper–Pearson event. -/
theorem bad_subset [NeZero N] (e : Fin N → Prop) (δ : ℝ) :
    bad (n := n) (b := b) e δ ⊆
      {seed | binomCdf n (sampledCount e (derive seed)) (poolRate e) ≤ δ} := by
  rintro seed ⟨k, p, hk, hp, hcdf, hpR⟩
  have hR := poolRate_mem_Icc e
  exact ((binomCdf_mono hk hR).trans
    (binomCdf_antitoneOn n k ⟨hp, hpR.le.trans hR.2⟩ hR hpR.le)).trans hcdf

/-- **Soundness of a pool-rate certificate.** For every property fixed before the seed, the
seeds on which a certificate read off the sample is wrong make up at most `(1 + N/2^b)ⁿ · δ`. -/
theorem rate_sound [NeZero N] (e : Fin N → Prop) {δ : ℝ} (hδ : 0 ≤ δ) :
    seedFrac (bad (n := n) (b := b) e δ) ≤ (1 + (N : ℝ) / 2 ^ b) ^ n * δ := by
  set A := univ.filter fun idx : Fin n → Fin N => binomCdf n (sampledCount e idx) (poolRate e) ≤ δ
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  -- Count: bad seeds ≤ seeds mapping into `A` ≤ `|A| (2^b/N + 1)ⁿ`.
  have hcard : ((univ.filter (· ∈ bad (n := n) (b := b) e δ)).card : ℝ) ≤
      A.card * ((2 : ℝ) ^ b / N + 1) ^ n := by
    have h1 : (univ.filter (· ∈ bad (n := n) (b := b) e δ)).card ≤
        (univ.filter fun seed : Fin n → Fin (2 ^ b) => derive seed ∈ A).card :=
      card_le_card fun seed hs => mem_filter.2 ⟨mem_univ _, mem_filter.2
        ⟨mem_univ _, bad_subset e δ (mem_filter.1 hs).2⟩⟩
    have h2' : ((2 ^ b / N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ b / N + 1 := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 ^ b) (n := N)
      push_cast at this ⊢
      linarith
    calc ((univ.filter (· ∈ bad (n := n) (b := b) e δ)).card : ℝ)
        ≤ ((A.card * (2 ^ b / N + 1) ^ n : ℕ) : ℝ) := by
          exact_mod_cast h1.trans (card_derive_preimage_le A)
      _ ≤ A.card * ((2 : ℝ) ^ b / N + 1) ^ n := by
          rw [Nat.cast_mul, Nat.cast_pow]; gcongr
  have hA := card_clopperPearson_le (n := n) e hδ
  -- Divide by `(2^b)ⁿ`: `(2^b/N + 1)ⁿ / (2^b)ⁿ = (1 + N/2^b)ⁿ / Nⁿ`.
  have hratio : ((2 : ℝ) ^ b / N + 1) ^ n / ((2 : ℝ) ^ b) ^ n =
      (1 + (N : ℝ) / 2 ^ b) ^ n / (N : ℝ) ^ n := by
    rw [← div_pow, ← div_pow]; congr 1; field_simp
  calc seedFrac (bad (n := n) (b := b) e δ)
      ≤ A.card * ((2 : ℝ) ^ b / N + 1) ^ n / ((2 : ℝ) ^ b) ^ n := by
        unfold seedFrac; gcongr
    _ = (1 + (N : ℝ) / 2 ^ b) ^ n * (A.card / (N : ℝ) ^ n) := by
        rw [mul_div_assoc, hratio]; ring
    _ ≤ (1 + (N : ℝ) / 2 ^ b) ^ n * δ := by gcongr

/-- **Selective publication.** An issuer commits `M` properties before the seed, then publishes
any certificate it likes, chosen after seeing the sample. The seeds on which the published claim
can be wrong make up at most `(1 + N/2^b)ⁿ · Σ δⱼ`. -/
theorem selective_sound [NeZero N] {M : ℕ} (e : Fin M → Fin N → Prop) {δ : Fin M → ℝ}
    (hδ : ∀ j, 0 ≤ δ j) :
    seedFrac (⋃ j, bad (n := n) (b := b) (e j) (δ j)) ≤
      (1 + (N : ℝ) / 2 ^ b) ^ n * ∑ j, δ j := by
  have hunion : (univ.filter (· ∈ ⋃ j, bad (n := n) (b := b) (e j) (δ j))) =
      univ.biUnion fun j => univ.filter (· ∈ bad (n := n) (b := b) (e j) (δ j)) := by
    ext seed; simp
  unfold seedFrac
  rw [hunion, mul_sum, div_le_iff₀ (by positivity), sum_mul]
  calc ((univ.biUnion fun j => univ.filter (· ∈ bad (n := n) (b := b) (e j) (δ j))).card : ℝ)
      ≤ ∑ j, ((univ.filter (· ∈ bad (n := n) (b := b) (e j) (δ j))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ j, (1 + (N : ℝ) / 2 ^ b) ^ n * δ j * ((2 : ℝ) ^ b) ^ n := by
        refine sum_le_sum fun j _ => ?_
        have := rate_sound (n := n) (b := b) (e j) (hδ j)
        unfold seedFrac at this
        rwa [div_le_iff₀ (by positivity)] at this

end OpenTheory.DesignSampling
