import OpenTheory.Optimization.OperatorNewtonSchulzAndNoiseScale

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix

namespace OpenTheory.OperatorNewtonSchulzAndNoiseScaleSmoke

open OpenTheory
open OpenTheory.OptimalTrainingRegimes
open OpenTheory.AlgorithmicOptimizerUnimprovability
open OpenTheory.FastestTrainingAndRoofline
open OpenTheory.MatrixSpectralPreconditioning
open OpenTheory.OperatorNewtonSchulzAndNoiseScale

-- Part 1: Matrix Newton–Schulz Polynomial Operator & Orthogonal Isometry Fixed-Point Theorem
#check @matrixNewtonSchulzStep
#check @IsRowOrthonormalMatrix
#check @IsColOrthonormalMatrix
#check @matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal
#check @matrixNewtonSchulzStep_fixed_point_of_colOrthonormal
#check @matrixNewtonSchulzStep_commutes_with_orthogonal

-- Part 2: Exact Singular-Value Cubic Convergence of Newton–Schulz
#check @newtonSchulzSingularMap
#check @newtonSchulzSingularMap_zero
#check @newtonSchulzSingularMap_one
#check @diagonal_matrixNewtonSchulzStep
#check @newtonSchulz_singular_cubic_convergence_and_basin

-- Part 3: Coupled 2x2 Symmetric Curvature Matrix Eigen-Decomposition
#check @coupledCurvatureMatrix2x2
#check @plusMode2
#check @minusMode2
#check @coupledCurvatureMatrix2x2_eigenvalues_and_condition_number

-- Part 4: Bochner Measure-Theoretic & Hilbert-Space Gradient Noise Scale
#check @hilbert_pairwise_orthogonal_norm_sq_sum
#check @hilbert_minibatch_variance_reduction_law
#check @measureGradVariance
#check @measureCriticalBatchCoordinate
#check @measure_stochastic_gradient_second_moment_decomposition

-- Part 5: Grand Operator Newton–Schulz & Measure-Theoretic Noise Scale Theorem
#check @operator_newton_schulz_and_noise_scale_grand_theorem

-- Smoke Test 1: Singular-Value Cubic Convergence of Newton–Schulz at σ = 1/2:
--   p(1/2) = (3/2)*(1/2) - (1/2)*(1/8) = 11/16 = 0.6875 > 1/2
--   1 - p(1/2) = 5/16 = (1/2)*(1 - 1/2)^2*(2 + 1/2) = (1/2)*(1/4)*(5/2) = 5/16
--   At the second step: p(p(1/2)) = p(11/16) = 7117/8192 ≈ 0.8688 > 11/16
example :
    newtonSchulzSingularMap 0 = 0 ∧
    newtonSchulzSingularMap 1 = 1 ∧
    newtonSchulzSingularMap (1 / 2) = 11 / 16 ∧
    (1 / 2 : ℝ) < newtonSchulzSingularMap (1 / 2) ∧
    newtonSchulzSingularMap (1 / 2) < 1 ∧
    1 - newtonSchulzSingularMap (1 / 2) = 5 / 16 ∧
    (1 / 2 : ℝ) * (1 - 1 / 2) ^ 2 * (2 + 1 / 2) = 5 / 16 ∧
    newtonSchulzSingularMap (newtonSchulzSingularMap (1 / 2)) = 7117 / 8192 ∧
    1 - newtonSchulzSingularMap (newtonSchulzSingularMap (1 / 2)) = 1075 / 8192 := by
  unfold newtonSchulzSingularMap
  norm_num

-- Smoke Test 2: Coupled 2x2 Curvature Matrix at ρ_off = 3/5:
--   Eigenvalues: 1 + 3/5 = 8/5 and 1 - 3/5 = 2/5
--   Condition number: (8/5) / (2/5) = 4 = diagonalPrecondConditionNumber (3/5)
--   Determinant: 1 - (3/5)^2 = 16/25, Trace: 2
example :
    coupledCurvatureMatrix2x2 (3 / 5) *ᵥ plusMode2 = (8 / 5 : ℝ) • plusMode2 ∧
    coupledCurvatureMatrix2x2 (3 / 5) *ᵥ minusMode2 = (2 / 5 : ℝ) • minusMode2 ∧
    Matrix.det (coupledCurvatureMatrix2x2 (3 / 5)) = 16 / 25 ∧
    Matrix.trace (coupledCurvatureMatrix2x2 (3 / 5)) = 2 ∧
    diagonalPrecondConditionNumber (3 / 5) = 4 := by
  obtain ⟨hplus, hminus, hdet, _, htrace, _⟩ :=
    coupledCurvatureMatrix2x2_eigenvalues_and_condition_number (3 / 5)
  have h1 : (1 + (3 / 5 : ℝ)) = 8 / 5 := by norm_num
  have h2 : (1 - (3 / 5 : ℝ)) = 2 / 5 := by norm_num
  have h3 : (1 - (3 / 5 : ℝ) ^ 2) = 16 / 25 := by norm_num
  have h4 : diagonalPrecondConditionNumber (3 / 5) = 4 := by
    unfold diagonalPrecondConditionNumber
    norm_num
  rw [h1] at hplus
  rw [h2] at hminus
  rw [h3] at hdet
  exact ⟨hplus, hminus, hdet, htrace, h4⟩

-- Smoke Test 3: Identity Matrix Is Fixed Point of `matrixNewtonSchulzStep`
example (n : ℕ) :
    matrixNewtonSchulzStep (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  apply matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal
  unfold IsRowOrthonormalMatrix
  simp

-- Axiom audits (confirming zero sorryAx)
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.matrixNewtonSchulzStep_fixed_point_of_colOrthonormal
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.matrixNewtonSchulzStep_commutes_with_orthogonal
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.diagonal_matrixNewtonSchulzStep
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.newtonSchulz_singular_cubic_convergence_and_basin
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.coupledCurvatureMatrix2x2_eigenvalues_and_condition_number
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.hilbert_pairwise_orthogonal_norm_sq_sum
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.hilbert_minibatch_variance_reduction_law
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.measure_stochastic_gradient_second_moment_decomposition
#print axioms OpenTheory.OperatorNewtonSchulzAndNoiseScale.operator_newton_schulz_and_noise_scale_grand_theorem

end OpenTheory.OperatorNewtonSchulzAndNoiseScaleSmoke
