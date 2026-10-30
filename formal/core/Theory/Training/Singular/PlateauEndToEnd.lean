import Theory.Training.Singular.StoppingRule
import Theory.Training.Singular.RRRLearningCoefficient

/-!
# End to end: the gradient-descent plateau pays the true dimension, Bayes pays `λ`

Two-layer linear network `y ≈ B A x`, whitened design, data matrix
`Ĉₙ = W₀ + n^{-1/2} Z` with `Z` an `N × M` matrix of i.i.d. `N(0,1)` entries, `W₀` with
`r` nonzero squared singular values, all `≥ s2 > 0`, and student width `r ≤ H ≤ min(M, N)`.
`gd_plateau_end_to_end` proves:

1. **Good event.** There are measurable bad events `badₙ` with `P(badₙ) → 0` such that
   off `badₙ`, for every SVD of `Ĉₙ` with positive decreasing singular values,
   gradient flow on `½‖B A - Ĉₙ‖²` from the aligned start `ε` reaches, at time
   `√(2/s2) log(1/ε)` and as `ε → 0`, exactly the truncated SVD `Ŵₙ = trunc (s2/2) Ĉₙ`.
2. **Risk.** `n · E‖Ŵₙ - W₀‖²_F → r (M + N - r)`.
3. **Comparison.** If `r < M`, `r < N`, `r < H`, the Bayes learning coefficient
   (Aoyagi–Watanabe, `rlct8 = 8λ`) satisfies `4 r (M+N-r) + 4 ≤ 8λ`, i.e.
   `r(M+N-r)/2 + 1/2 ≤ λ`: the plateau's asymptotic error `r(M+N-r)/2` (the KL is half the
   squared error) is strictly below Bayes' `λ`.

Assumptions not proved here: the formula for `λ` and Watanabe's `n E[G_Bayes] → λ` are
cited; the initialization is aligned with the data's singular vectors (the random small
initialization case is Jiang–Chen–Ding 2023); positivity of all singular values of `Ĉₙ`
(true almost surely) is a hypothesis.
-/

noncomputable section
open Set Real Filter Topology Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRisk OpenTheory.TruncationRank OpenTheory.TruncationEvent

namespace OpenTheory.Plateau

variable {M N H : ℕ}

local notation "EM" => EuclideanSpace ℝ (Fin M)
local notation "EN" => EuclideanSpace ℝ (Fin N)
local notation "Noise" => EuclideanSpace ℝ (Fin N × Fin M)

/-- The data matrix `W₀ + n^{-1/2} Z(x)`, as an operator. -/
def dataOp (W₀ : Matrix (Fin N) (Fin M) ℝ) (n : ℕ) (x : Noise) : EM →ₗ[ℝ] EN :=
  toEuclideanLin W₀ + (Real.sqrt n)⁻¹ •
    noiseOp (EuclideanSpace.basisFun (Fin M) ℝ) (EuclideanSpace.basisFun (Fin N) ℝ) x

/-- Chebyshev for the Gaussian norm: `P(a < c ‖x‖) ≤ c² E‖x‖² / a²`. -/
theorem measure_lt_norm_le {c a : ℝ} (ha : 0 < a) :
    stdGaussian Noise {x | a < c * ‖x‖} ≤
      ENNReal.ofReal ((∫ x, (c * ‖x‖) ^ 2 ∂stdGaussian Noise) / a ^ 2) := by
  have hint : Integrable (fun x : Noise => (c * ‖x‖) ^ 2) (stdGaussian Noise) := by
    simpa [mul_pow] using (GaussianQuadratic.integrable_norm_pow (G := Noise) 2).const_mul (c ^ 2)
  calc stdGaussian Noise {x | a < c * ‖x‖}
      ≤ stdGaussian Noise {x | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal ((c * ‖x‖) ^ 2)} := by
        refine measure_mono fun x hx => ?_
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le (le_of_lt hx) 2)
    _ ≤ (∫⁻ x, ENNReal.ofReal ((c * ‖x‖) ^ 2) ∂stdGaussian Noise) / ENNReal.ofReal (a ^ 2) :=
        meas_ge_le_lintegral_div (by fun_prop) (by simp [ha.ne']) ENNReal.ofReal_ne_top
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _),
          ENNReal.ofReal_div_of_pos (by positivity)]

/-- **Good event.** For any `h > 0`, outside measurable events of vanishing probability,
`‖Ĉₙ Ĉₙᵀ - W₀ W₀ᵀ‖ ≤ h`. -/
theorem good_event (W₀ : Matrix (Fin N) (Fin M) ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ bad : ℕ → Set Noise, (∀ n, MeasurableSet (bad n)) ∧
      Tendsto (fun n => stdGaussian Noise (bad n)) atTop (𝓝 0) ∧
      ∀ n, 1 ≤ n → ∀ x ∉ bad n,
        opn (gramL (dataOp W₀ n x) - gramL (toEuclideanLin W₀)) ≤ h := by
  set bE := EuclideanSpace.basisFun (Fin M) ℝ
  set bF := EuclideanSpace.basisFun (Fin N) ℝ
  set w := opn (toEuclideanLin W₀)
  have hw : 0 ≤ w := opn_nonneg _
  obtain ⟨c₀, hc₀, hc⟩ := exists_hs_le bE (noiseOp bE bF)
  set κ := min 1 (h / (2 * w + 1))
  have hκ : 0 < κ := lt_min one_pos (by positivity)
  have hκ2 : κ * (2 * w + 1) ≤ h := by
    have := min_le_right 1 (h / (2 * w + 1))
    calc κ * (2 * w + 1) ≤ h / (2 * w + 1) * (2 * w + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = h := by field_simp
  refine ⟨fun n => {x | κ * Real.sqrt n < (c₀ + 1) * ‖x‖}, fun n => ?_, ?_, ?_⟩
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · set K := ∫ x, ((c₀ + 1) * ‖x‖) ^ 2 ∂stdGaussian Noise
    have hbound : ∀ n : ℕ, 1 ≤ n → stdGaussian Noise {x | κ * Real.sqrt n < (c₀ + 1) * ‖x‖} ≤
        ENNReal.ofReal (K / κ ^ 2 / n) := by
      intro n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine (measure_lt_norm_le (by positivity)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [mul_pow κ, Real.sq_sqrt hn'.le, div_div]
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K / κ ^ 2 / n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat _)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le)
      ((eventually_ge_atTop 1).mono fun n hn => hbound n hn)
  · intro n hn x hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
    set D := (Real.sqrt n)⁻¹ • noiseOp bE bF x
    have hD : hs bE D ≤ κ := by
      rw [hs_smul, abs_of_pos (inv_pos.2 hs0), inv_mul_le_iff₀ hs0]
      have := hc x
      have hx' : (c₀ + 1) * ‖x‖ ≤ κ * Real.sqrt n := not_lt.1 hx
      nlinarith [norm_nonneg x]
    have hop : opn D ≤ κ := (opNorm_le_hs bE D).trans hD
    have h1 := opn_gramL_sub_le (dataOp W₀ n x) (toEuclideanLin W₀)
    rw [show dataOp W₀ n x - toEuclideanLin W₀ = D from add_sub_cancel_left _ _] at h1
    have h2 : opn D * (2 * w + opn D) ≤ κ * (2 * w + 1) :=
      mul_le_mul hop (by linarith [min_le_left 1 (h / (2 * w + 1))])
        (by linarith [opn_nonneg D]) hκ.le
    linarith

/-- **End-to-end theorem** (see the module docstring). -/
theorem gd_plateau_end_to_end (hHM : H ≤ M) (hHN : H ≤ N) (W₀ : Matrix (Fin N) (Fin M) ℝ)
    {s2 : ℝ} (hs2 : 0 < s2)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EN i = 0)
    (hWR : ∀ i, (gramR_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EM i ∉ Set.Ici s2 →
      (gramR_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EM i = 0)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W₀)) finrank_EN (Set.Ici s2) ≤ H) :
    -- 1. the plateau is the truncated SVD, off events of vanishing probability
    (∃ bad : ℕ → Set Noise, (∀ n, MeasurableSet (bad n)) ∧
      Tendsto (fun n => stdGaussian Noise (bad n)) atTop (𝓝 0) ∧
      ∀ n, 1 ≤ n → ∀ x ∉ bad n,
        ∀ (U : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin M) (Fin M) ℝ) (σ : ℕ → ℝ),
        U * Uᵀ = 1 → V * Vᵀ = 1 → Uᵀ * toEuclideanLin.symm (dataOp W₀ n x) * V = diagData σ →
        Antitone σ → ∀ σmin, 0 < σmin → (∀ k, σmin ≤ σ k) →
        ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H,
          (∀ t, HasDerivAt f (gradField (toEuclideanLin.symm (dataOp W₀ n x)) (f t)) t) →
          rotate U V (f 0) = initState ε → ∀ i j,
            |prodBA (f (√(2 / s2) * log (1 / ε))) i j -
              toEuclideanLin.symm (trunc finrank_EN (dataOp W₀ n x) (s2 / 2)) i j| < δ) ∧
    -- 2. its risk is the dimension of the rank-`r` manifold
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal
        (n * hs (EuclideanSpace.basisFun (Fin M) ℝ)
          (trunc finrank_EN (dataOp W₀ n x) (s2 / 2) - toEuclideanLin W₀) ^ 2) ∂stdGaussian Noise)
      atTop (𝓝 (ENNReal.ofReal
        ((countIn (gramL_isSymmetric (toEuclideanLin W₀)) finrank_EN (Set.Ici s2) : ℝ) *
          (M + N - countIn (gramL_isSymmetric (toEuclideanLin W₀)) finrank_EN (Set.Ici s2))))) ∧
    -- 3. Bayes pays more
    (∀ r : ℤ, r < M → r < N → r < H → 4 * r * (M + N - r) + 4 ≤ RRR.rlct8 M N H r) := by
  obtain ⟨bad, hmeas, hlim, hgood⟩ := good_event W₀ (h := s2 / 4) (by positivity)
  refine ⟨⟨bad, hmeas, hlim, ?_⟩, ?_, ?_⟩
  · intro n hn x hx U V σ hU hV hsvd hanti σmin hmin hσ δ hδ
    have hclose : opn (gramL (toEuclideanLin (toEuclideanLin.symm (dataOp W₀ n x))) -
        gramL (toEuclideanLin W₀)) ≤ s2 / 4 := by
      rw [LinearEquiv.apply_symm_apply]; exact hgood n hn x hx
    have := plateau_eq_trunc hHM hHN hU hV hsvd hanti hmin hσ hs2 hWL hclose hrH hδ
    simpa only [LinearEquiv.apply_symm_apply] using this
  · exact tendsto_risk_iid finrank_EM finrank_EN _ _ (by positivity : (0 : ℝ) < s2 / 2)
      (by linarith) hWL hWR
  · intro r hrM hrN hrH'
    exact RRR.rlct8_gain hrM hrN hrH'

/-- **The stopping rule, end to end.** For any fixed `0 < ρ ≤ s2/4`, outside events of
vanishing probability, stopping gradient flow at `(3/2) ×` the first time the training loss
drops below `ρ` gives, as `ε → 0`, the truncated SVD, whose risk is `r(M+N-r)`
(`gd_plateau_end_to_end`). -/
theorem stopping_rule_end_to_end (hHM : H ≤ M) (hHN : H ≤ N) (W₀ : Matrix (Fin N) (Fin M) ℝ)
    {s2 ρ : ℝ} (hs2 : 0 < s2) (hρ0 : 0 < ρ) (hρ : ρ ≤ s2 / 4)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W₀)).eigenvalues finrank_EN i = 0)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W₀)) finrank_EN (Set.Ici s2) ≤ H) :
    ∃ bad : ℕ → Set Noise, (∀ n, MeasurableSet (bad n)) ∧
      Tendsto (fun n => stdGaussian Noise (bad n)) atTop (𝓝 0) ∧
      ∀ n, 1 ≤ n → ∀ x ∉ bad n,
        ∀ (U : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin M) (Fin M) ℝ) (σ : ℕ → ℝ),
        U * Uᵀ = 1 → V * Vᵀ = 1 → Uᵀ * toEuclideanLin.symm (dataOp W₀ n x) * V = diagData σ →
        Antitone σ → ∀ σmin, 0 < σmin → (∀ k, σmin ≤ σ k) →
        ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H,
          (∀ t, HasDerivAt f (gradField (toEuclideanLin.symm (dataOp W₀ n x)) (f t)) t) →
          rotate U V (f 0) = initState ε → ∀ i j,
            |prodBA (f (3 / 2 * hitTime (toEuclideanLin.symm (dataOp W₀ n x)) f ρ)) i j -
              toEuclideanLin.symm (trunc finrank_EN (dataOp W₀ n x) (s2 / 2)) i j| < δ := by
  set h := min (s2 / 8) (ρ / (2 * (N + 1)))
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hh8 : h ≤ s2 / 8 := min_le_left _ _
  have hNh : N * h < ρ := by
    have h1 : h ≤ ρ / (2 * (N + 1)) := min_le_right _ _
    have h2 : (N : ℝ) * (ρ / (2 * (N + 1))) < ρ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    calc (N : ℝ) * h ≤ N * (ρ / (2 * (N + 1))) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ < ρ := h2
  obtain ⟨bad, hmeas, hlim, hgood⟩ := good_event W₀ hh
  refine ⟨bad, hmeas, hlim, ?_⟩
  intro n hn x hx U V σ hU hV hsvd hanti σmin hmin hσ δ hδ
  have hclose : opn (gramL (toEuclideanLin (toEuclideanLin.symm (dataOp W₀ n x))) -
      gramL (toEuclideanLin W₀)) ≤ h := by
    rw [LinearEquiv.apply_symm_apply]; exact hgood n hn x hx
  have := stopping_rule hHM hHN hU hV hsvd hanti hmin hσ hs2 hh.le hh8 hWL hclose hrH hNh hρ hδ
  simpa only [LinearEquiv.apply_symm_apply] using this

end OpenTheory.Plateau
