import OpenTheory.Architectures.HilbertMLAAndDistributionSpeculative

noncomputable section

open scoped BigOperators RealInnerProductSpace

open OpenTheory
open OpenTheory.FastestTrainingAndRoofline
open OpenTheory.LongContextAndFastInference
open OpenTheory.HilbertMLAAndDistributionSpeculative

-- Part 1: Hilbert-Space Multi-Head Latent Attention (MLA) Orthogonal Projection & Logit Preservation
#check @IsSelfAdjointIdempotentProjection
#check @IsSelfAdjointIdempotentProjection.map_sub_self
#check @IsSelfAdjointIdempotentProjection.inner_proj_sub_self
#check @IsSelfAdjointIdempotentProjection.inner_proj_left_sub_self
#check @IsSelfAdjointIdempotentProjection.norm_sq_eq_add_norm_sq
#check @hilbert_mla_projection_pythagorean_and_logit_exactness

-- Part 2: Finite-Dimensional Rank-r Orthonormal Latent Dictionary & Truncation Error
#check @fullKeyEnergy
#check @latentProjectedEnergy
#check @residualTailEnergy
#check @mla_spectral_tail_truncation_conservation

-- Part 3: Exact Pointwise & Total-Variation Distribution-Level Lossless Speculative Decoding
#check @IsTokenPMF
#check @speculativeAcceptedMass
#check @speculativeResidualDeficit
#check @speculativeAcceptanceRate
#check @speculativeRejectionRate
#check @totalVariationDistance
#check @speculativeEmittedPMF
#check @speculativeEmittedPMF_eq_target
#check @two_mul_speculativeAcceptedMass_eq
#check @distribution_level_lossless_speculative_sampling_theorem

-- Part 4: Grand Hilbert MLA & Distribution-Level Speculative Decoding Synthesis
#check @hilbert_mla_and_distribution_speculative_grand_theorem

-- Smoke Test 1: Concrete Fin 3 Spectral Energy Conservation under Rank-2 Latent Projection
-- Suppose d_full = 3 with spectral singular coordinates coeff = ![3, 4, 12],
-- and S = {0, 1} is the rank-2 principal latent subspace:
--   latentProjectedEnergy S coeff = 3^2 + 4^2 = 9 + 16 = 25
--   residualTailEnergy S coeff    = 12^2 = 144
--   fullKeyEnergy coeff           = 25 + 144 = 169 = 13^2
def sampleKeyCoeff : Fin 3 → ℝ := ![3, 4, 12]
def sampleLatentSet : Finset (Fin 3) := {0, 1}

example :
    latentProjectedEnergy sampleLatentSet sampleKeyCoeff = 25 ∧
    residualTailEnergy sampleLatentSet sampleKeyCoeff = 144 ∧
    fullKeyEnergy sampleKeyCoeff = 169 ∧
    latentProjectedEnergy sampleLatentSet sampleKeyCoeff +
      residualTailEnergy sampleLatentSet sampleKeyCoeff =
      fullKeyEnergy sampleKeyCoeff := by
  have hcons := (mla_spectral_tail_truncation_conservation sampleLatentSet sampleKeyCoeff).1
  have hlat : latentProjectedEnergy sampleLatentSet sampleKeyCoeff = 25 := by
    unfold latentProjectedEnergy sampleLatentSet sampleKeyCoeff
    have h01 : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
    rw [Finset.sum_insert h01, Finset.sum_singleton]
    norm_num
  have hfull : fullKeyEnergy sampleKeyCoeff = 169 := by
    unfold fullKeyEnergy sampleKeyCoeff
    rw [Fin.sum_univ_three]
    norm_num
  have hres : residualTailEnergy sampleLatentSet sampleKeyCoeff = 144 := by
    linarith
  exact ⟨hlat, hres, hfull, hcons⟩

-- Smoke Test 2: Concrete Fin 3 Token PMFs for Lossless Speculative Sampling
-- Target distribution p_target = ![1/2, 1/3, 1/6]
-- Draft distribution  p_draft  = ![1/4, 1/2, 1/4]
-- Accepted masses: min(1/4, 1/2) = 1/4, min(1/2, 1/3) = 1/3, min(1/4, 1/6) = 1/6
-- Acceptance rate α = 1/4 + 1/3 + 1/6 = 3/4
-- Residual deficits: max(0, 1/4) = 1/4, max(0, -1/6) = 0, max(0, -1/12) = 0
-- Rejection rate 1 - α = 1/4 + 0 + 0 = 1/4 = TV(p_target, p_draft)
-- Emitted PMF: ![1/4 + 1/4, 1/3 + 0, 1/6 + 0] = ![1/2, 1/3, 1/6] = p_target!
def sampleTargetPMF : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]
def sampleDraftPMF : Fin 3 → ℝ := ![1 / 4, 1 / 2, 1 / 4]

theorem sampleTargetPMF_isTokenPMF : IsTokenPMF (Fin 3) sampleTargetPMF := by
  refine ⟨?_, ?_⟩
  · intro x
    fin_cases x <;> norm_num [sampleTargetPMF]
  · rw [Fin.sum_univ_three]
    norm_num [sampleTargetPMF]

theorem sampleDraftPMF_isTokenPMF : IsTokenPMF (Fin 3) sampleDraftPMF := by
  refine ⟨?_, ?_⟩
  · intro x
    fin_cases x <;> norm_num [sampleDraftPMF]
  · rw [Fin.sum_univ_three]
    norm_num [sampleDraftPMF]

example :
    (∀ x : Fin 3, speculativeEmittedPMF sampleTargetPMF sampleDraftPMF x = sampleTargetPMF x) ∧
    speculativeAcceptanceRate sampleTargetPMF sampleDraftPMF = 3 / 4 ∧
    speculativeRejectionRate sampleTargetPMF sampleDraftPMF = 1 / 4 ∧
    totalVariationDistance sampleTargetPMF sampleDraftPMF = 1 / 4 ∧
    speculativeAcceptanceRate sampleTargetPMF sampleDraftPMF +
      speculativeRejectionRate sampleTargetPMF sampleDraftPMF = 1 := by
  have hthm :=
    distribution_level_lossless_speculative_sampling_theorem
      sampleTargetPMF_isTokenPMF sampleDraftPMF_isTokenPMF
  refine ⟨hthm.1, ?_, ?_, ?_, hthm.2.2.1.1⟩
  · unfold speculativeAcceptanceRate speculativeAcceptedMass
    rw [Fin.sum_univ_three]
    norm_num [sampleTargetPMF, sampleDraftPMF]
  · unfold speculativeRejectionRate speculativeResidualDeficit
    rw [Fin.sum_univ_three]
    norm_num [sampleTargetPMF, sampleDraftPMF]
  · unfold totalVariationDistance
    rw [Fin.sum_univ_three]
    norm_num [sampleTargetPMF, sampleDraftPMF]

-- Axiom audits (confirming zero sorryAx)
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.IsSelfAdjointIdempotentProjection.inner_proj_sub_self
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.IsSelfAdjointIdempotentProjection.norm_sq_eq_add_norm_sq
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.hilbert_mla_projection_pythagorean_and_logit_exactness
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.mla_spectral_tail_truncation_conservation
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.speculativeEmittedPMF_eq_target
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.two_mul_speculativeAcceptedMass_eq
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.distribution_level_lossless_speculative_sampling_theorem
#print axioms OpenTheory.HilbertMLAAndDistributionSpeculative.hilbert_mla_and_distribution_speculative_grand_theorem
