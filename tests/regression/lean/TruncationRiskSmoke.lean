import LearningTheory.Singular.TruncationRank
import LearningTheory.Singular.PlateauEndToEnd
import LearningTheory.Singular.BalancedPlateau

open OpenTheory

-- The statistics step: n·E‖trunc − W‖² → r(M+N−r), standard axioms only.
#print axioms OpenTheory.Perturbation.second_order_bound
#print axioms OpenTheory.GaussianQuadratic.integral_norm_sq_map
#print axioms OpenTheory.TruncationRisk.tendsto_risk
#print axioms OpenTheory.TruncationRank.rankL_eq_rankR
#print axioms OpenTheory.TruncationRank.tendsto_risk_iid

-- 4×4, rank 1: the limit r(M+N−r) is 7 (= 2λ_regular of the rank-1 manifold).
example : (1 : ℝ) * (4 + 4 - 1) = 7 := by norm_num

-- End to end: plateau = truncated SVD on the good event, its risk → r(M+N−r), Bayes pays more.
#print axioms OpenTheory.Plateau.plateau_eq_trunc
#print axioms OpenTheory.Plateau.gd_plateau_end_to_end
#print axioms OpenTheory.Plateau.stopping_rule
#print axioms OpenTheory.Plateau.stopping_rule_end_to_end
-- Balanced (non-aligned) initialization: Riccati closed form, uniqueness, entry limits, plateau.
#print axioms OpenTheory.Riccati.hasDerivAt_Pc
#print axioms OpenTheory.Riccati.eq_Pc
#print axioms OpenTheory.Riccati.Pc_entries_limit
#print axioms OpenTheory.Plateau.hasDerivAt_Pop
#print axioms OpenTheory.Plateau.balanced_plateau_diag
#print axioms OpenTheory.Plateau.balanced_plateau_eq_trunc
