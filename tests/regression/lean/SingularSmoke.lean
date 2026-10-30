import Theory.Training.Singular.NormalCrossing
import Theory.Training.Singular.AnalyticRLCT
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open OpenTheory.Singular

-- `y = a b² x`: K = a² b⁴ with a uniform prior has λ = 1/4, the coefficient of
-- `bayes_second_moment` at α = 1/2.
example : IsRLCT (monomialLoss ![1, 2]) (monomialPrior ![0, 0]) (MeasureTheory.volume.restrict (cube 2))
    (1 / 4) := by
  convert isRLCT_toy (k := 2) (by norm_num) using 1
  norm_num

-- A regular two-parameter model, K = a² b²: λ = 1/2 is attained in both coordinates (m = 2).
example : IsRLCT (monomialLoss ![1, 1]) (monomialPrior ![0, 0]) (MeasureTheory.volume.restrict (cube 2))
    (1 / 2) :=
  isRLCT_monomial _ _ ⟨0, by simp, by norm_num⟩ fun i _ => by fin_cases i <;> norm_num

-- The free energy of K = a² b⁴ grows at most like (1/4) log n.
example {n : ℝ} (hn : 1 ≤ n) :
    -Real.log (partition ![1, 2] ![0, 0] n) ≤
      ((0 : ℝ) + 1) / (2 * 2) * Real.log n + 1 + ∑ i : Fin 2, Real.log ((![0, 0] i : ℝ) + 1) := by
  simpa using freeEnergy_le ![1, 2] ![0, 0] (i₀ := 1) (by norm_num) hn

#print axioms exists_resolution_monomial_bounds
#print axioms isRLCT_monomial
#print axioms zeta_monomial
#print axioms freeEnergy_le

/-! The hypotheses of `exists_isRLCT` are satisfiable: `K(y) = y₀²` on `ℝ¹` with a bump prior. -/

open Filter Topology in
example : ∃ lam : ℚ, 0 < lam ∧
    IsRLCT (fun y : EuclideanSpace ℝ (Fin 1) => y 0 ^ 2)
      (ContDiffBump.mk (c := (0 : EuclideanSpace ℝ (Fin 1))) 1 2 one_pos one_lt_two)
      MeasureTheory.volume lam := by
  set b : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb0 : 0 < b 0 := b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 1), x 0 = 0 → ‖x‖ = 0 := fun x hx => by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, hx]; simp
  refine exists_isRLCT ⊤ ?_ ?_ (fun _ _ => sq_nonneg _) b.continuous b.hasCompactSupport
    (by simp) ?_ ⟨0, subset_tsupport _ (Function.mem_support.2 hb0.ne'), by simp⟩
  · exact (((EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).analyticOnNhd _).pow 2)
  · intro x _ h
    simp only [ne_eq, not_not, pow_eq_zero_iff two_ne_zero] at h
    -- along `x + t e₀`, the first coordinate is `x 0 + t`
    let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have hcont : Tendsto (fun t : ℝ => x + t • e) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun t : ℝ => x + t • e) := by fun_prop
      simpa using this.tendsto 0
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually h)
    have h0 := @hball 0 (by simpa using hε)
    have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    simp [e] at h0 h1
    linarith
  · intro x _ hx
    have hx0 : x 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
    exact b.pos_of_mem_ball (by rw [mem_ball_zero_iff, hnorm x hx0]; exact b.rOut_pos)

#print axioms exists_isRLCT
