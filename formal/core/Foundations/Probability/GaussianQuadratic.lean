import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Quadratic functionals of a standard Gaussian vector

For the standard Gaussian `μ = stdGaussian G` on a finite-dimensional real inner-product
space `G` (Mathlib):

* `integral_inner_mul_inner`: `∫ ⟪u, x⟫ ⟪v, x⟫ dμ = ⟪u, v⟫`;
* `integral_norm_sq_map`: `∫ ‖L x‖² dμ = Σₐ ‖L (g a)‖²` for any linear map `L` and any
  orthonormal basis `g` of `G` (the Gaussian "trace" identity);
* `integrable_one_add_norm_pow`: every polynomial moment is finite (Fernique).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OpenTheory.GaussianQuadratic

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem integrable_norm_pow (k : ℕ) : Integrable (fun x : G => ‖x‖ ^ k) (stdGaussian G) :=
  (IsGaussian.memLp_id (stdGaussian G) k (by simp)).integrable_norm_pow'

theorem integrable_one_add_norm_pow (k : ℕ) :
    Integrable (fun x : G => (1 + ‖x‖) ^ k) (stdGaussian G) := by
  refine (((integrable_const (1 : ℝ)).add (integrable_norm_pow (G := G) k)).const_mul
    (2 ^ k)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases le_total ‖x‖ 1 with h | h
  · calc (1 + ‖x‖) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + ‖x‖ ^ k) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + ‖x‖) ^ k ≤ (2 * ‖x‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * ‖x‖ ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + ‖x‖ ^ k) := by gcongr; linarith

theorem integrable_inner_mul_inner (u v : G) :
    Integrable (fun x : G => ⟪u, x⟫ * ⟪v, x⟫) (stdGaussian G) := by
  refine ((integrable_norm_pow (G := G) 2).const_mul (‖u‖ * ‖v‖)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |⟪u, x⟫| * |⟪v, x⟫| ≤ (‖u‖ * ‖x‖) * (‖v‖ * ‖x‖) :=
        mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
          (by positivity)
    _ = ‖u‖ * ‖v‖ * ‖x‖ ^ 2 := by ring

/-- The covariance of the standard Gaussian is the inner product. -/
theorem integral_inner_mul_inner (u v : G) :
    ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(stdGaussian G) = ⟪u, v⟫ := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian G)) u v
  rw [covarianceBilin_stdGaussian, innerSL_apply_apply] at h
  simpa [integral_id_stdGaussian] using h.symm

/-- **Gaussian trace identity**: `E ‖L x‖² = Σₐ ‖L (g a)‖²`. -/
theorem integral_norm_sq_map {α F : Type*} [Fintype α] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (g : OrthonormalBasis α ℝ G) (L : G →ₗ[ℝ] F) :
    ∫ x, ‖L x‖ ^ 2 ∂(stdGaussian G) = ∑ a, ‖L (g a)‖ ^ 2 := by
  classical
  have hx : ∀ x, ‖L x‖ ^ 2 = ∑ a, ∑ c, (⟪g a, x⟫ * ⟪g c, x⟫) * ⟪L (g a), L (g c)⟫ := by
    intro x
    conv_lhs => rw [← g.sum_repr' x]
    rw [← real_inner_self_eq_norm_sq, map_sum, sum_inner]
    simp_rw [inner_sum, map_smul, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  simp_rw [hx]
  rw [integral_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun c _ => (integrable_inner_mul_inner _ _).mul_const _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun c _ => (integrable_inner_mul_inner _ _).mul_const _]
  simp_rw [integral_mul_const, integral_inner_mul_inner, g.inner_eq_ite]
  simp

theorem integrable_norm_sq_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (L : G →ₗ[ℝ] F) :
    Integrable (fun x => ‖L x‖ ^ 2) (stdGaussian G) := by
  set T := LinearMap.toContinuousLinearMap L
  refine ((integrable_norm_pow (G := G) 2).const_mul (‖T‖ ^ 2)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2

end OpenTheory.GaussianQuadratic
