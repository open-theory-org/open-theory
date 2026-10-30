import Theory.Training.Singular.PlateauModes
import Theory.Training.Singular.RRRLearningCoefficient
import Theory.Training.Singular.PlateauFlow
import Theory.Training.Singular.ScaleInvariantPrior

open OpenTheory.Plateau OpenTheory.RRR

-- The 4×4 network of the experiments: λ = 7 for r = 1, H = 4 (8λ = 56), true dimension 3.5.
example : rlct8 4 4 4 1 = 56 := by decide
example : 4 * 1 * (4 + 4 - 1) + 4 ≤ rlct8 4 4 4 1 := rlct8_gain (by norm_num) (by norm_num) (by norm_num)

-- The closed form starts at ε².
example : mode 1 (1 / 10) 0 = (1 / 10) ^ 2 := mode_zero (by norm_num) (by norm_num)

#print axioms OpenTheory.Plateau.plateau
#print axioms OpenTheory.RRR.rlct8_gain

-- Mode decoupling: a solution exists, and every solution has the logistic product.
example : ∃ f : ℝ → OpenTheory.Plateau.State 3 3 2, f 0 = OpenTheory.Plateau.initState (1 / 10) ∧
    ∀ t, HasDerivAt f (OpenTheory.Plateau.gradField (OpenTheory.Plateau.diagData fun _ => 1) (f t)) t :=
  OpenTheory.Plateau.flow_exists (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)

#print axioms OpenTheory.Plateau.flow_decouples
#print axioms OpenTheory.Plateau.flow_plateau
#print axioms OpenTheory.Plateau.rotate_solves

-- Bayes side: E[m(z)²] = α under N(0,1) for the prior |u|^{α-1}; α = 1/2 gives λ = 1/4.
example : ∫ z, OpenTheory.BayesToy.postMean (1 / 2) z ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 / 2 :=
  OpenTheory.BayesToy.bayes_second_moment (by norm_num)

#print axioms OpenTheory.BayesToy.bayes_second_moment
