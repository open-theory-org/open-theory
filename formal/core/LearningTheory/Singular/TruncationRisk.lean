import Foundations.LinearAlgebra.Perturbation
import Foundations.Probability.GaussianQuadratic

/-!
# Asymptotic risk of the truncated-SVD estimator under Gaussian noise

Observation model: `C_n = W + n^{-1/2} Φ(x)` with `x ~ stdGaussian G` and `Φ : G → (E → F)`
linear (for i.i.d. `N(0,1)` matrix entries, `Φ` is the coordinate isomorphism, see
`TruncationRank`). Estimator: `trunc τ C = P_{[τ,∞)}(C Cᵀ) ∘ C`, the hard-thresholded SVD.
If every nonzero eigenvalue of `W Wᵀ` and `Wᵀ W` is `≥ s2` and `0 < τ < s2`, then

  `n · E ‖trunc τ (C_n) - W‖²_HS  →  Σₐ ‖P_T(Φ gₐ)‖²_HS`   (`tendsto_risk`),

where `P_T D = D - P⊥ D Q⊥` is the projection onto the tangent space of the rank-`r`
matrices at `W`, and `g` is any orthonormal basis of `G`. The expectation is the lower
Lebesgue integral `∫⁻`, so no measurability of the estimator is needed.

Proof: `second_order_bound` gives `|√n (trunc - W) - P_T(Φ x)|_HS ≤ K(‖x‖)/√n` with `K`
polynomial; Gaussian moments (Fernique) make the envelope integrable; the limit is
squeezed between two convergent integrals; the value is the Gaussian trace identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation

namespace OpenTheory.TruncationRisk

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)
variable {ι : Type*} [Fintype ι]

/-- Hard-thresholded SVD: keep the singular directions of `C` with `σ² ≥ τ`. -/
def trunc (C : E →ₗ[ℝ] F) (τ : ℝ) : E →ₗ[ℝ] F := Ptop hF C τ ∘ₗ C

/-- Projection onto the tangent space at `W` of the manifold of matrices of rank `rank W`. -/
def tangent (W : E →ₗ[ℝ] F) (s2 : ℝ) (D : E →ₗ[ℝ] F) : E →ₗ[ℝ] F :=
  D - Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2

theorem tangent_smul (W : E →ₗ[ℝ] F) (s2 c : ℝ) (D : E →ₗ[ℝ] F) :
    tangent hE hF W s2 (c • D) = c • tangent hE hF W s2 D := by
  ext x; simp [tangent, smul_sub]

theorem tangent_add (W : E →ₗ[ℝ] F) (s2 : ℝ) (D D' : E →ₗ[ℝ] F) :
    tangent hE hF W s2 (D + D') = tangent hE hF W s2 D + tangent hE hF W s2 D' := by
  ext x; simp only [tangent, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add]; abel

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hs_smul (b : OrthonormalBasis ι ℝ E) (c : ℝ) (T : E →ₗ[ℝ] F) :
    hs b (c • T) = |c| * hs b T := by
  rw [hs, hs, show cols b (c • T) = c • cols b T from rfl, norm_smul, Real.norm_eq_abs]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hs_le_add_sub (b : OrthonormalBasis ι ℝ E) (T U : E →ₗ[ℝ] F) :
    hs b T ≤ hs b U + hs b (T - U) := by
  simpa using hs_add_le b U (T - U)

theorem hs_tangent_le (b : OrthonormalBasis ι ℝ E) (W : E →ₗ[ℝ] F) (s2 : ℝ) (D : E →ₗ[ℝ] F) :
    hs b (tangent hE hF W s2 D) ≤ 2 * hs b D := by
  have h1 := hs_comp_left_le b (Pbot hF W s2) (D ∘ₗ Qbot hE W s2)
  have h2 := hs_comp_right_le b (stdOrthonormalBasis ℝ F) D (Qbot hE W s2)
  have p1 : opn (Pbot hF W s2) ≤ 1 := opn_spectralProjection_le (gramL_isSymmetric W) hF _
  have p2 : opn (Qbot hE W s2) ≤ 1 := opn_spectralProjection_le (gramR_isSymmetric W) hE _
  have h3 : hs b (Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2) ≤ hs b D := by
    calc _ ≤ opn (Pbot hF W s2) * hs b (D ∘ₗ Qbot hE W s2) := h1
      _ ≤ 1 * (hs b D * 1) := mul_le_mul p1 (h2.trans (mul_le_mul_of_nonneg_left p2
          (hs_nonneg _ _))) (hs_nonneg _ _) zero_le_one
      _ = hs b D := by ring
  have := hs_sub_le b D (Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2)
  rw [tangent]; linarith

/-- `|e - a| ≤ ε` implies `|e² - a²| ≤ ε (2a + ε)`. -/
theorem abs_sq_sub_sq_le {e a ε : ℝ} (he : 0 ≤ e) (ha : 0 ≤ a) (h : |e - a| ≤ ε) :
    |e ^ 2 - a ^ 2| ≤ ε * (2 * a + ε) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans h
  rw [abs_le] at h
  rw [show e ^ 2 - a ^ 2 = (e - a) * (e + a) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ e + a)]
  exact mul_le_mul (abs_le.2 h) (by linarith) (by linarith) hε

/-- Polynomial size of the second-order remainder. -/
def kfun (w hsW δ τ h : ℝ) : ℝ :=
  (h * (2 * w + h)) ^ 2 * (hsW / δ ^ 2) + 2 * (h * (2 * w + h)) * h * (1 / δ + 1 / τ)

theorem kfun_nonneg {w hsW δ τ h : ℝ} (hw : 0 ≤ w) (hW : 0 ≤ hsW) (hδ : 0 < δ) (hτ : 0 < τ)
    (hh : 0 ≤ h) : 0 ≤ kfun w hsW δ τ h := by
  unfold kfun
  have : 0 ≤ 1 / δ + 1 / τ := by positivity
  positivity

/-- The scalar part of the remainder estimate. -/
theorem scalar_bound {s v h w hsW δ τ a b : ℝ} (hs1 : 1 ≤ s) (hv : 0 ≤ v) (hvh : v ≤ h / s)
    (hw : 0 ≤ w) (hW : 0 ≤ hsW) (hδ : 0 < δ) (hτ : 0 < τ) (ha0 : 0 ≤ a)
    (ha : a ≤ v * (2 * w + v)) (hb0 : 0 ≤ b) (hb : b ≤ v * (2 * w + v)) :
    s * (a / δ * (b / δ) * hsW + (a / δ + a / τ + (b / δ + b / τ)) * v) ≤
      kfun w hsW δ τ h / s := by
  have hs0 : 0 < s := by linarith
  have hh : 0 ≤ h := by
    have := mul_nonneg (hv.trans hvh) hs0.le
    rwa [div_mul_cancel₀ _ hs0.ne'] at this
  have hvh' : v ≤ h := hvh.trans (div_le_self hh hs1)
  set A := h * (2 * w + h) / s
  have hA : v * (2 * w + v) ≤ A := by
    rw [show A = h / s * (2 * w + h) by ring]
    exact mul_le_mul hvh (by linarith) (by linarith) (div_nonneg hh hs0.le)
  have hA0 : 0 ≤ A := by positivity
  have e1 : a * b ≤ A * A := mul_le_mul (ha.trans hA) (hb.trans hA) hb0 hA0
  have e2 : (a + b) * v ≤ (2 * A) * (h / s) := mul_le_mul (by linarith) hvh hv (by linarith)
  have hα : 0 ≤ hsW / δ ^ 2 := div_nonneg hW (sq_nonneg _)
  have hβ : 0 ≤ 1 / δ + 1 / τ := by positivity
  calc s * (a / δ * (b / δ) * hsW + (a / δ + a / τ + (b / δ + b / τ)) * v)
      = s * ((a * b) * (hsW / δ ^ 2) + ((a + b) * v) * (1 / δ + 1 / τ)) := by ring
    _ ≤ s * ((A * A) * (hsW / δ ^ 2) + ((2 * A) * (h / s)) * (1 / δ + 1 / τ)) := by
        gcongr
    _ = kfun w hsW δ τ h / s := by
        simp only [kfun, A]; field_simp

/-- **Deterministic remainder.** For `C = W + D`, `s ≥ 1` and `hs(s D) ≤ h`,

  `hs(s (trunc C - W) - P_T(s D)) ≤ K(h) / s`. -/
theorem remainder_bound (b : OrthonormalBasis ι ℝ E) {W D : E →ₗ[ℝ] F} {s2 τ s h : ℝ}
    (hτ : 0 < τ) (hτs : τ < s2)
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0)
    (hs1 : 1 ≤ s) (hD : hs b (s • D) ≤ h) :
    hs b (s • (trunc hF (W + D) τ - W) - tangent hE hF W s2 (s • D)) ≤
      kfun (opn W) (hs b W) (s2 - τ) τ h / s := by
  have hs0 : 0 < s := by linarith
  have key := second_order_bound hE hF b (stdOrthonormalBasis ℝ F) (C := W + D) (W := W)
    hτ hτs hWL hWR
  rw [add_sub_cancel_left] at key
  have e : s • (trunc hF (W + D) τ - W) - tangent hE hF W s2 (s • D) =
      s • (Ptop hF (W + D) τ ∘ₗ (W + D) - W - (D - Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2)) := by
    rw [tangent_smul, ← smul_sub]; rfl
  rw [e, hs_smul, abs_of_pos hs0]
  set v := hs b D
  have hv : 0 ≤ v := hs_nonneg _ _
  have hvh : v ≤ h / s := by
    rw [le_div_iff₀ hs0, mul_comm]; rwa [hs_smul, abs_of_pos hs0] at hD
  have hop : opn D ≤ v := opNorm_le_hs b D
  have hw := opn_nonneg W
  have hgl : opn (gramL W - gramL (W + D)) ≤ v * (2 * opn W + v) := by
    rw [opn_sub_comm]
    have := opn_gramL_sub_le (W + D) W
    rw [add_sub_cancel_left] at this
    exact this.trans (mul_le_mul hop (by linarith) (by linarith [opn_nonneg D]) hv)
  have hgr : opn (gramR W - gramR (W + D)) ≤ v * (2 * opn W + v) := by
    rw [opn_sub_comm]
    have := opn_gramR_sub_le (W + D) W
    rw [add_sub_cancel_left] at this
    exact this.trans (mul_le_mul hop (by linarith) (by linarith [opn_nonneg D]) hv)
  calc s * hs b (Ptop hF (W + D) τ ∘ₗ (W + D) - W - (D - Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2))
      ≤ s * (opn (gramL W - gramL (W + D)) / (s2 - τ) *
          (opn (gramR W - gramR (W + D)) / (s2 - τ)) * hs b W +
        (opn (gramL W - gramL (W + D)) / (s2 - τ) + opn (gramL W - gramL (W + D)) / τ +
          (opn (gramR W - gramR (W + D)) / (s2 - τ) + opn (gramR W - gramR (W + D)) / τ)) * v) :=
        mul_le_mul_of_nonneg_left key hs0.le
    _ ≤ _ := scalar_bound hs1 hv hvh hw (hs_nonneg _ _) (by linarith) hτ (opn_nonneg _) hgl
        (opn_nonneg _) hgr

/-- Polynomial envelope: `K(cρ) (4cρ + K(cρ)) ≤ K(c) (4c + K(c)) ρ⁸` for `ρ ≥ 1`. -/
theorem envelope_le {w hsW δ τ c ρ : ℝ} (hw : 0 ≤ w) (hW : 0 ≤ hsW) (hδ : 0 < δ) (hτ : 0 < τ)
    (hc : 0 ≤ c) (hρ : 1 ≤ ρ) :
    kfun w hsW δ τ (c * ρ) * (4 * (c * ρ) + kfun w hsW δ τ (c * ρ)) ≤
      kfun w hsW δ τ c * (4 * c + kfun w hsW δ τ c) * ρ ^ 8 := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hα : 0 ≤ hsW / δ ^ 2 := div_nonneg hW (sq_nonneg _)
  have hβ : 0 ≤ 1 / δ + 1 / τ := by positivity
  have r2 : ρ ≤ ρ ^ 2 := by nlinarith
  have r34 : ρ ^ 3 ≤ ρ ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  have r14 : ρ ≤ ρ ^ 4 := by
    calc ρ = ρ ^ 1 := (pow_one ρ).symm
      _ ≤ ρ ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  set U := c * (2 * w + c)
  have hU : 0 ≤ U := by positivity
  have hu : c * ρ * (2 * w + c * ρ) ≤ U * ρ ^ 2 := by
    have := mul_nonneg (mul_nonneg hw hc) (by linarith : 0 ≤ ρ ^ 2 - ρ)
    simp only [U]; nlinarith
  have hu0 : 0 ≤ c * ρ * (2 * w + c * ρ) := by positivity
  have hK : kfun w hsW δ τ (c * ρ) ≤ kfun w hsW δ τ c * ρ ^ 4 := by
    simp only [kfun]
    have e1 : (c * ρ * (2 * w + c * ρ)) ^ 2 ≤ U ^ 2 * ρ ^ 4 := by
      calc _ ≤ (U * ρ ^ 2) ^ 2 := pow_le_pow_left₀ hu0 hu 2
        _ = U ^ 2 * ρ ^ 4 := by ring
    have e2 : c * ρ * (2 * w + c * ρ) * (c * ρ) ≤ U * c * ρ ^ 4 := by
      calc _ ≤ U * ρ ^ 2 * (c * ρ) := mul_le_mul_of_nonneg_right hu (by positivity)
        _ = U * c * ρ ^ 3 := by ring
        _ ≤ U * c * ρ ^ 4 := mul_le_mul_of_nonneg_left r34 (by positivity)
    calc (c * ρ * (2 * w + c * ρ)) ^ 2 * (hsW / δ ^ 2) +
          2 * (c * ρ * (2 * w + c * ρ)) * (c * ρ) * (1 / δ + 1 / τ)
        = (c * ρ * (2 * w + c * ρ)) ^ 2 * (hsW / δ ^ 2) +
          2 * (c * ρ * (2 * w + c * ρ) * (c * ρ)) * (1 / δ + 1 / τ) := by ring
      _ ≤ U ^ 2 * ρ ^ 4 * (hsW / δ ^ 2) + 2 * (U * c * ρ ^ 4) * (1 / δ + 1 / τ) := by
          gcongr
      _ = _ := by simp only [U]; ring
  have hK0 : 0 ≤ kfun w hsW δ τ (c * ρ) := kfun_nonneg hw hW hδ hτ (by positivity)
  have hK1 : 0 ≤ kfun w hsW δ τ c := kfun_nonneg hw hW hδ hτ hc
  calc kfun w hsW δ τ (c * ρ) * (4 * (c * ρ) + kfun w hsW δ τ (c * ρ))
      ≤ (kfun w hsW δ τ c * ρ ^ 4) * (4 * c * ρ ^ 4 + kfun w hsW δ τ c * ρ ^ 4) := by
        apply mul_le_mul hK _ (by positivity) (by positivity)
        have : 4 * (c * ρ) ≤ 4 * c * ρ ^ 4 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r14 hc)
            (by norm_num)
        linarith
    _ = _ := by ring

section Gaussian

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- `x ↦ Φ(x) y`. -/
def evalMap (Φ : G →ₗ[ℝ] (E →ₗ[ℝ] F)) (y : E) : G →ₗ[ℝ] F where
  toFun x := Φ x y
  map_add' x x' := by simp
  map_smul' c x := by simp

/-- `x ↦ P_T(Φ x) y`. -/
def tangentEval (W : E →ₗ[ℝ] F) (s2 : ℝ) (Φ : G →ₗ[ℝ] (E →ₗ[ℝ] F)) (y : E) : G →ₗ[ℝ] F where
  toFun x := tangent hE hF W s2 (Φ x) y
  map_add' x x' := by simp [tangent_add]
  map_smul' c x := by simp [tangent_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace G] [BorelSpace G] in
theorem exists_hs_le (b : OrthonormalBasis ι ℝ E) (Φ : G →ₗ[ℝ] (E →ₗ[ℝ] F)) :
    ∃ c, 0 ≤ c ∧ ∀ x, hs b (Φ x) ≤ c * ‖x‖ := by
  refine ⟨Real.sqrt (∑ i, opn (evalMap Φ (b i)) ^ 2), Real.sqrt_nonneg _, fun x => ?_⟩
  rw [← sq_le_sq₀ (hs_nonneg _ _) (by positivity), mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), hs_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le (evalMap Φ (b i)) x) 2

/-- **Asymptotic risk of the truncated SVD.** With noise `n^{-1/2} Φ(x)`, `x ~ stdGaussian G`,

  `n · E ‖trunc τ (W + n^{-1/2} Φ x) - W‖²_HS → Σₐ ‖P_T(Φ (g a))‖²_HS`. -/
theorem tendsto_risk (b : OrthonormalBasis ι ℝ E) {α : Type*} [Fintype α]
    (g : OrthonormalBasis α ℝ G) (Φ : G →ₗ[ℝ] (E →ₗ[ℝ] F)) {W : E →ₗ[ℝ] F} {s2 τ : ℝ}
    (hτ : 0 < τ) (hτs : τ < s2)
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0) :
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal
        (n * hs b (trunc hF (W + (Real.sqrt n)⁻¹ • Φ x) τ - W) ^ 2) ∂(stdGaussian G))
      atTop (𝓝 (ENNReal.ofReal (∑ a, hs b (tangent hE hF W s2 (Φ (g a))) ^ 2))) := by
  obtain ⟨c, hc0, hc⟩ := exists_hs_le b Φ
  have hδ : 0 < s2 - τ := by linarith
  set K1 := kfun (opn W) (hs b W) (s2 - τ) τ c
  set M := K1 * (4 * c + K1)
  -- the limit integrand and the envelope
  set A : G → ℝ := fun x => ∑ i, ‖tangentEval hE hF W s2 Φ (b i) x‖ ^ 2
  set Env : G → ℝ := fun x => M * (1 + ‖x‖) ^ 8
  have hA : ∀ x, A x = hs b (tangent hE hF W s2 (Φ x)) ^ 2 := fun x => by rw [hs_sq]; rfl
  have hA0 : ∀ x, 0 ≤ A x := fun x => by rw [hA]; positivity
  have hM : 0 ≤ M := mul_nonneg (kfun_nonneg (opn_nonneg _) (hs_nonneg _ _) hδ hτ hc0)
    (add_nonneg (by positivity) (kfun_nonneg (opn_nonneg _) (hs_nonneg _ _) hδ hτ hc0))
  have hEnv0 : ∀ x, 0 ≤ Env x := fun x => by positivity
  have Ameas : Measurable A := by
    refine (continuous_finsetSum _ fun i _ => ?_).measurable
    exact ((tangentEval hE hF W s2 Φ (b i)).continuous_of_finiteDimensional.norm.pow 2)
  have Envmeas : Measurable Env := by fun_prop
  have Aint : Integrable A (stdGaussian G) :=
    integrable_finsetSum _ fun i _ => GaussianQuadratic.integrable_norm_sq_map _
  have Envint : Integrable Env (stdGaussian G) :=
    (GaussianQuadratic.integrable_one_add_norm_pow 8).const_mul M
  -- pointwise estimate
  have point : ∀ n : ℕ, 1 ≤ n → ∀ x : G,
      |n * hs b (trunc hF (W + (Real.sqrt n)⁻¹ • Φ x) τ - W) ^ 2 - A x| ≤
        (Real.sqrt n)⁻¹ * Env x := by
    intro n hn x
    set s := Real.sqrt n
    have hs1 : 1 ≤ s := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have hs0 : 0 < s := by linarith
    set h := c * (1 + ‖x‖)
    have hsD : s • ((Real.sqrt n)⁻¹ • Φ x) = Φ x := by
      rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    have hΦh : hs b (Φ x) ≤ h := (hc x).trans (mul_le_mul_of_nonneg_left (by linarith) hc0)
    have rb := remainder_bound hE hF b hτ hτs hWL hWR hs1 (D := s⁻¹ • Φ x)
      (h := h) (by rw [hsD]; exact hΦh)
    rw [hsD] at rb
    set T := trunc hF (W + s⁻¹ • Φ x) τ - W
    set K := kfun (opn W) (hs b W) (s2 - τ) τ h
    have hK0 : 0 ≤ K := kfun_nonneg (opn_nonneg _) (hs_nonneg _ _) hδ hτ (by positivity)
    have hdiff : |hs b (s • T) - hs b (tangent hE hF W s2 (Φ x))| ≤ K / s := by
      rw [abs_le]
      have h1 := hs_le_add_sub b (s • T) (tangent hE hF W s2 (Φ x))
      have h2 := hs_le_add_sub b (tangent hE hF W s2 (Φ x)) (s • T)
      have h3 : hs b (tangent hE hF W s2 (Φ x) - s • T) = hs b (s • T - tangent hE hF W s2 (Φ x)) := by
        rw [← hs_neg, neg_sub]
      rw [h3] at h2
      constructor <;> linarith
    have hsq := abs_sq_sub_sq_le (hs_nonneg _ _) (hs_nonneg _ _) hdiff
    rw [hs_smul, abs_of_pos hs0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← hA] at hsq
    have ha2 : hs b (tangent hE hF W s2 (Φ x)) ≤ 2 * h :=
      (hs_tangent_le hE hF b W s2 (Φ x)).trans (by linarith)
    have hKs : K / s ≤ K := div_le_self hK0 hs1
    have henv := envelope_le (opn_nonneg W) (hs_nonneg b W) hδ hτ hc0
      (by linarith [norm_nonneg x] : 1 ≤ 1 + ‖x‖)
    calc _ ≤ K / s * (2 * hs b (tangent hE hF W s2 (Φ x)) + K / s) := hsq
      _ ≤ K / s * (4 * h + K) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hK0 hs0.le); linarith
      _ = s⁻¹ * (K * (4 * h + K)) := by ring
      _ ≤ s⁻¹ * Env x := mul_le_mul_of_nonneg_left henv (inv_nonneg.2 hs0.le)
  -- the squeeze
  set L := ∫⁻ x, ENNReal.ofReal (A x) ∂(stdGaussian G)
  set I := ∫⁻ x, ENNReal.ofReal (Env x) ∂(stdGaussian G)
  have hI : I ≠ ⊤ := (Envint.lintegral_lt_top).ne
  have hL : L ≠ ⊤ := (Aint.lintegral_lt_top).ne
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    exact tendsto_inv_atTop_zero.comp
      ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  have hrI : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)⁻¹ * I) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hr (Or.inr hI)
  have upper : ∀ᶠ n : ℕ in atTop, ∫⁻ x, ENNReal.ofReal
      (n * hs b (trunc hF (W + (Real.sqrt n)⁻¹ • Φ x) τ - W) ^ 2) ∂(stdGaussian G) ≤
        L + ENNReal.ofReal (Real.sqrt n)⁻¹ * I := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← lintegral_const_mul _ Envmeas.ennreal_ofReal,
      ← lintegral_add_left Ameas.ennreal_ofReal]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_add (hA0 x) (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hEnv0 x))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := point n hn x
    rw [abs_le] at this; linarith
  have lower : ∀ᶠ n : ℕ in atTop, L - ENNReal.ofReal (Real.sqrt n)⁻¹ * I ≤
      ∫⁻ x, ENNReal.ofReal
        (n * hs b (trunc hF (W + (Real.sqrt n)⁻¹ • Φ x) τ - W) ^ 2) ∂(stdGaussian G) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [tsub_le_iff_right, ← lintegral_const_mul _ Envmeas.ennreal_ofReal,
      ← lintegral_add_right _ (Envmeas.ennreal_ofReal.const_mul _)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    have := point n hn x
    rw [abs_le] at this; linarith
  have hlim : L = ENNReal.ofReal (∑ a, hs b (tangent hE hF W s2 (Φ (g a))) ^ 2) := by
    change ∫⁻ x, ENNReal.ofReal (A x) ∂(stdGaussian G) = _
    rw [← ofReal_integral_eq_lintegral_ofReal Aint (Filter.Eventually.of_forall hA0)]
    congr 1
    simp only [A]
    rw [integral_finsetSum _ fun i _ => GaussianQuadratic.integrable_norm_sq_map _]
    simp_rw [GaussianQuadratic.integral_norm_sq_map g, hs_sq]
    exact Finset.sum_comm
  rw [← hlim]
  have h1 := ENNReal.Tendsto.sub (tendsto_const_nhds (x := L)) hrI (Or.inl hL)
  have h2 := (tendsto_const_nhds (x := L)).add hrI
  rw [tsub_zero] at h1; rw [add_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 lower upper

end Gaussian

end OpenTheory.TruncationRisk
