import Specs.Basic
import Specs.HeldOut
import Specs.PoolRate
import Specs.JudgedRate
import Scopes.OnRegion

/-!
# The claim templates as instances of one construction

Each claim template of the repository is a specification (an observable, a domain and an
aggregate, `Specs.Basic`) whose certificates give the guarantee `Sound`: the probability that the check accepts a false
claim is at most `δ`, uniformly over the parameters the certifier chooses after seeing the
evidence. These theorems are the meaning of every certificate; the registries in `specs/` and the
catalog refer to them by name. See `docs/specs.md`.

| Template | Observable | Domain | Aggregate | Randomness | δ |
| --- | --- | --- | --- | --- | --- |
| `OnRegion` | property: predicts `c` | region (a box) | all | none | `0` |
| `heldout-error` | property: wrong | distribution `D` | rate ≤ `p` | IID sample from any `D` | `δ` |
| `pool-rate` | property: the event | committed pool | rate ≤ `p` | beacon seed | `(1 + N/2^b)ⁿ δ` |
| `judged-rate` | property: the true event | committed pool | rate ≤ `pJ + pA` | beacon seed, judge + gold audit | `(1 + N/2^b)ⁿ δJ + (1 + N/2^b)ᵐ δA` |
-/

open MeasureTheory

namespace OpenTheory

/-! ## Region: exact -/

/-- **`OnRegion`.** For every box `b` and class `c` the region check accepts, the TorchLean model
predicts `c` on every real input of `b`. -/
theorem onRegion_sound {m k : ℕ} (g : Exact.Net m k) (r : g.Rules Exact.IntervalRule)
    (θ : g.Params) :
    Sound (Measure.dirac ())
      (fun _ (bc : Exact.Box × Fin k) => OnRegion.certify g r θ bc.1 bc.2 = true)
      (fun bc => (⟨.property fun θ x => Predicts (g.eval θ x) bc.2,
        .region {x | Exact.InBox bc.1 x}, .all⟩ : Spec g.Params (TorchLean.Tensor ℝ [m])).Target θ) 0 := by
  rw [sound_exact_iff]
  rintro ⟨b, c⟩ h
  exact fun x hx => (OnRegion.certify_sound g r θ b c h).2 x hx

/-! ## Population: IID sample -/

/-- **`heldout-error`.** For every data distribution `D`, the probability that the sample admits a
count `k` and a bound `p` passing the exact binomial test while the population error rate exceeds
`p` is at most `δ` (Clopper–Pearson, uniform in `k` and `p`). -/
theorem heldOut_sound {H Z : Type*} [MeasurableSpace Z] {ℓ : H → Z → ℝ} {h : H} {n : ℕ}
    (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h)) (δ : ℝ)
    (D : Measure Z) [IsProbabilityMeasure D] :
    Sound (StatLean.StatisticalLearning.sampleLaw D n)
      (fun s (kp : ℕ × ℝ) => BinomialTail.numErrors ℓ s h ≤ kp.1 ∧ 0 ≤ kp.2 ∧
        BinomialTail.binomCdf n kp.1 kp.2 ≤ δ)
      (fun kp => (⟨.property fun h z => ℓ h z = 1, .distribution ‹_› D, .meanLe kp.2⟩ :
        Spec H Z).Target h) δ := by
  refine (measure_mono fun s hs => ?_).trans (BinomialTail.clopperPearson h01 hmeas δ)
  obtain ⟨⟨k, p⟩, ⟨hk, hp, hcdf⟩, hnot⟩ := hs
  simp only [Spec.target_meanLe_distribution, not_le] at hnot
  rw [← BinomialTail.risk_eq_measureReal h01 hmeas] at hnot
  exact BinomialTail.mem_clopperPearson_event h01 hmeas hk hp hcdf hnot

/-! ## Population: design-based sample of a committed pool -/

/-- The uniform law of the beacon seeds. -/
noncomputable def seedLaw (n b : ℕ) : Measure (Fin n → Fin (2 ^ b)) :=
  (PMF.uniformOfFintype (Fin n → Fin (2 ^ b))).toMeasure

/-- The seed law of a set is its fraction of seeds. -/
theorem seedLaw_apply {n b : ℕ} (S : Set (Fin n → Fin (2 ^ b))) :
    seedLaw n b S = ENNReal.ofReal (DesignSampling.seedFrac S) := by
  classical
  rw [seedLaw, PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite S).measurableSet,
    DesignSampling.seedFrac, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  · rw [ENNReal.ofReal_natCast]
    congr 1
    exact Fintype.card_subtype _
  · rw [← ENNReal.ofReal_natCast]; push_cast; rfl

open Classical in
/-- The pool rate of `e` is its fraction of pool items (whatever the decidability instance). -/
theorem poolRate_eq_card {N : ℕ} (e : Fin N → Prop) :
    DesignSampling.poolRate e = ((Finset.univ.filter fun j => e j).card : ℝ) / N := by
  unfold DesignSampling.poolRate; congr 3

/-- **`pool-rate`.** For every property `e` fixed before the seed, the probability over seeds that
the claim holds for some count and bound `p` while more than a fraction `p` of the pool has `e` is
at most `(1 + N/2^b)ⁿ · δ`. -/
theorem poolRate_sound {N n b : ℕ} [NeZero N] (e : Fin N → Prop) [DecidablePred e] {δ : ℝ}
    (hδ : 0 ≤ δ) :
    Sound (seedLaw n b)
      (fun seed (kp : ℕ × ℝ) =>
        PoolRate.Claim (fun i => decide (e (DesignSampling.derive seed i))) kp.1 kp.2 δ)
      (fun kp => (⟨.property fun (_ : Unit) j => e j, .pool N id, .meanLe kp.2⟩ :
        Spec Unit (Fin N)).Target ())
      ((1 + (N : ℝ) / 2 ^ b) ^ n * δ) := by
  have hsub : {seed : Fin n → Fin (2 ^ b) | ∃ kp : ℕ × ℝ,
      PoolRate.Claim (fun i => decide (e (DesignSampling.derive seed i))) kp.1 kp.2 δ ∧
      ¬ (⟨.property fun (_ : Unit) j => e j, .pool N id, .meanLe kp.2⟩ :
        Spec Unit (Fin N)).Target ()} ⊆ DesignSampling.bad e δ := by
    rintro seed ⟨⟨k, p⟩, hc, hnot⟩
    simp only [Spec.target_meanLe_pool, id, not_le] at hnot
    exact (PoolRate.Claim.sound e seed hc).resolve_left (by rw [poolRate_eq_card, not_le]; convert hnot)
  unfold Sound
  refine (measure_mono hsub).trans ?_
  rw [seedLaw_apply]
  exact ENNReal.ofReal_le_ofReal (DesignSampling.rate_sound e hδ)

/-! ## Population: pool graded by a judge, audited against gold labels -/

/-- **`judged-rate`.** The probability over seeds that the claim holds for some counts and bounds
while the true failure rate exceeds `pJ + pA` is at most `(1 + N/2^b)ⁿ · δJ + (1 + N/2^b)ᵐ · δA`. -/
theorem judgedRate_sound {N n m b : ℕ} [NeZero N] (eT eJ : Fin N → Prop) [DecidablePred eT]
    [DecidablePred eJ] (h : m ≤ n) {δJ δA : ℝ} (hJ : 0 ≤ δJ) (hA : 0 ≤ δA) :
    Sound (seedLaw n b)
      (fun s (ps : ℕ × ℕ × ℝ × ℝ) =>
        JudgedRate.Claim (fun i => decide (eJ (DesignSampling.derive s i)))
          (fun i => decide (JudgedRate.missed eT eJ
            (DesignSampling.derive (DesignSampling.prefixSeed h s) i)))
          ps.1 ps.2.1 ps.2.2.1 ps.2.2.2 δJ δA)
      (fun ps => (⟨.property fun (_ : Unit) j => eT j, .pool N id, .meanLe (ps.2.2.1 + ps.2.2.2)⟩ :
        Spec Unit (Fin N)).Target ())
      ((1 + (N : ℝ) / 2 ^ b) ^ n * δJ + (1 + (N : ℝ) / 2 ^ b) ^ m * δA) := by
  unfold Sound
  refine (measure_mono (t := JudgedRate.bad eT eJ h δJ δA 0) ?_).trans ?_
  · rintro s ⟨⟨kJ, kA, pJ, pA⟩, hc, hnot⟩
    simp only [Spec.target_meanLe_pool, id, not_le] at hnot
    exact (JudgedRate.Claim.sound eT eJ h s hc).resolve_left
      (by rw [poolRate_eq_card, not_le]; convert hnot)
  · rw [seedLaw_apply]
    refine ENNReal.ofReal_le_ofReal ((JudgedRate.bad_frac eT eJ h hJ hA le_rfl).trans ?_)
    simp

/-- **`judged-rate` with the false-alarm term.** Target `pJ + pA + pB − 1`; `δB` adds
`(1 + N/2^b)ᵐ · δB` to the bound. -/
theorem judgedRate_alarms_sound {N n m b : ℕ} [NeZero N] (eT eJ : Fin N → Prop)
    [DecidablePred eT] [DecidablePred eJ] (h : m ≤ n) {δJ δA δB : ℝ} (hJ : 0 ≤ δJ) (hA : 0 ≤ δA)
    (hB : 0 ≤ δB) :
    Sound (seedLaw n b)
      (fun s (ps : (ℕ × ℕ × ℕ) × (ℝ × ℝ × ℝ)) =>
        JudgedRate.Claim (fun i => decide (eJ (DesignSampling.derive s i)))
          (fun i => decide (JudgedRate.missed eT eJ
            (DesignSampling.derive (DesignSampling.prefixSeed h s) i)))
          ps.1.1 ps.1.2.1 ps.2.1 ps.2.2.1 δJ δA ∧
        PoolRate.Claim (fun i => decide (JudgedRate.notAlarm eT eJ
          (DesignSampling.derive (DesignSampling.prefixSeed h s) i))) ps.1.2.2 ps.2.2.2 δB)
      (fun ps => (⟨.property fun (_ : Unit) j => eT j, .pool N id,
        .meanLe (ps.2.1 + ps.2.2.1 + ps.2.2.2 - 1)⟩ : Spec Unit (Fin N)).Target ())
      ((1 + (N : ℝ) / 2 ^ b) ^ n * δJ + (1 + (N : ℝ) / 2 ^ b) ^ m * (δA + δB)) := by
  unfold Sound
  refine (measure_mono (t := JudgedRate.bad eT eJ h δJ δA δB) ?_).trans ?_
  · rintro s ⟨⟨⟨kJ, kA, kB⟩, ⟨pJ, pA, pB⟩⟩, ⟨hc, hb⟩, hnot⟩
    simp only [Spec.target_meanLe_pool, id, not_le] at hnot
    exact (JudgedRate.Claim.sound_alarms eT eJ h s hc hb).resolve_left
      (by rw [poolRate_eq_card, not_le]; convert hnot)
  · rw [seedLaw_apply]
    exact ENNReal.ofReal_le_ofReal (by
      have := JudgedRate.bad_frac (b := b) eT eJ h hJ hA hB
      linarith)

end OpenTheory
