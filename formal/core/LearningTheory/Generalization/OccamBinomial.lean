import Verification.Statistical.BinomialTail

/-!
# The binomial Occam bound for countable hypothesis spaces

Give each hypothesis `h` of a countable space a prior weight `w h` with
`Σ' h, w h ≤ 1` (for a prefix-free code with lengths `L h`, the Kraft weights
`w h = 2^(-L h)`). With probability at least `1 - δ` over `n` IID observations,
simultaneously for every hypothesis, the observed error count is not in the
lower `δ · w h` tail of `Binomial(n, R_h)` (`occam_binomial`). The hypothesis may
be chosen after seeing the sample, so this bounds the population error of a
trained network from its training errors alone. On a realized sample, a
network with at most `k` errors and `P(Bin(n,p) ≤ k) ≤ δ · w h` either has
population error at most `p` or the sample lies in the `δ`-event
(`mem_occamEvent`).

The weights compose: a two-part code (a header from one code, then a payload
from a code that may depend on the header) gives the product weights on the
sigma type (`tsum_sigma_mul_le_one`), and a payload drawn uniformly from a
finite set has total weight one (`tsum_uniformWeight`).
-/

noncomputable section
open MeasureTheory StatLean.StatisticalLearning
open scoped ENNReal

namespace OpenTheory.BinomialTail

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D] {n : ℕ}

/-- Some hypothesis has its observed error count in the lower `δ · w h` tail. -/
def occamEvent (ℓ : H → Z → ℝ) (D : Measure Z) (w : H → ℝ≥0∞) (n : ℕ) (δ : ℝ) :
    Set (Sample Z n) :=
  {s | ∃ h, binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ * (w h).toReal}

/-- **Binomial Occam bound.** For a countable hypothesis space with `{0,1}`
losses and prior weights summing to at most one, the event that some hypothesis
has its error count in its lower `δ · w h` binomial tail has probability at most `δ`. -/
theorem occam_binomial [Countable H] {ℓ : H → Z → ℝ} (h01 : ∀ h z, ℓ h z = 0 ∨ ℓ h z = 1)
    (hmeas : ∀ h, Measurable (ℓ h)) {w : H → ℝ≥0∞} (hw : ∑' h, w h ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    sampleLaw D n (occamEvent ℓ D w n δ) ≤ ENNReal.ofReal δ := by
  have hfin : ∀ h, w h ≠ ∞ := fun h =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum h).trans hw)
  have hU : occamEvent ℓ D w n δ =
      ⋃ h, {s : Sample Z n | binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ * (w h).toReal} := by
    ext s; simp [occamEvent]
  calc sampleLaw D n (occamEvent ℓ D w n δ)
      ≤ ∑' h, sampleLaw D n
          {s : Sample Z n | binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ * (w h).toReal} :=
        hU ▸ measure_iUnion_le _
    _ ≤ ∑' h, ENNReal.ofReal δ * w h := ENNReal.tsum_le_tsum fun h =>
        (clopperPearson (h01 h) (hmeas h) _).trans
          (by rw [ENNReal.ofReal_mul hδ, ENNReal.ofReal_toReal (hfin h)])
    _ = ENNReal.ofReal δ * ∑' h, w h := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal δ := by
        simpa using mul_le_mul_right hw (ENNReal.ofReal δ)

/-- Reading the bound off a realized sample. -/
theorem mem_occamEvent {ℓ : H → Z → ℝ} {w : H → ℝ≥0∞} {h : H}
    (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h)) {s : Sample Z n} {k : ℕ}
    {p δ : ℝ} (hk : numErrors ℓ s h ≤ k) (hp : 0 ≤ p) (hcdf : binomCdf n k p ≤ δ * (w h).toReal)
    (hpR : p < risk D ℓ h) : s ∈ occamEvent ℓ D w n δ :=
  ⟨h, mem_clopperPearson_event h01 hmeas hk hp hcdf hpR⟩

/-! ### Composing prior weights -/

omit [MeasurableSpace Z] in
/-- **Two-part codes.** Header weights summing to at most one, and for each
header payload weights summing to at most one, give weights on the sigma type
summing to at most one. -/
theorem tsum_sigma_mul_le_one {ι : Type*} {X : ι → Type*} {v : ι → ℝ≥0∞}
    {u : ∀ i, X i → ℝ≥0∞} (hv : ∑' i, v i ≤ 1) (hu : ∀ i, ∑' x, u i x ≤ 1) :
    ∑' p : Σ i, X i, v p.1 * u p.1 p.2 ≤ 1 := by
  rw [ENNReal.tsum_sigma']
  calc ∑' i, ∑' x, v i * u i x = ∑' i, v i * ∑' x, u i x :=
        tsum_congr fun i => ENNReal.tsum_mul_left
    _ ≤ ∑' i, v i * 1 := ENNReal.tsum_le_tsum fun i => mul_le_mul_right (hu i) _
    _ ≤ 1 := by simpa using hv

/-- Uniform weights on a finite set `A`. -/
def uniformWeight {X : Type*} (A : Set X) [Fintype A] (x : X) : ℝ≥0∞ :=
  by classical exact if x ∈ A then (Fintype.card A : ℝ≥0∞)⁻¹ else 0

omit [MeasurableSpace Z] in
theorem tsum_uniformWeight {X : Type*} (A : Set X) [Fintype A] :
    ∑' x, uniformWeight A x ≤ 1 := by
  classical
  rw [show (fun x => uniformWeight A x) = A.indicator fun _ => (Fintype.card A : ℝ≥0∞)⁻¹ by
    funext x; simp [uniformWeight, Set.indicator], ← tsum_subtype, tsum_fintype,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card A) with h0 | hpos
  · simp [h0]
  · exact (ENNReal.mul_inv_cancel (by exact_mod_cast hpos.ne') (by simp)).le

end OpenTheory.BinomialTail
