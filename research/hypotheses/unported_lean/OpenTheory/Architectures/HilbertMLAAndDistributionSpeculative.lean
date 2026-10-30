import OpenTheory.Architectures.LongContextAndFastInference
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Phase 18 Module 2 (Option A.2): Hilbert-Space Multi-Head Latent Attention (MLA) Orthogonal Projection Calculus & Exact Distribution-Level Lossless Speculative Decoding

How does Multi-Head Latent Attention (MLA) project high-dimensional key-value tensors into a
low-rank latent subspace of an arbitrary real Hilbert space `H` while satisfying an exact
Pythagorean reconstruction law and Cauchy–Schwarz attention logit error bound, and how does
modified rejection sampling in speculative decoding guarantee zero pointwise and total-variation
distributional distortion (`p_emitted(x) = p_target(x)` for every token `x : V`) while achieving
single-step acceptance probability `α = 1 - TV(p_target, p_draft)`?

This module formalizes and proves **Phase 18 Module 2** in
`OpenTheory.HilbertMLAAndDistributionSpeculative` with **zero `sorry`s**:

1. **Part 1: Hilbert-Space Multi-Head Latent Attention (MLA) Orthogonal Projection & Exact Attention
   Logit Preservation (`IsSelfAdjointIdempotentProjection`,
   `hilbert_mla_projection_pythagorean_and_logit_exactness`)**:
   - In any real inner product space `H`, for any continuous linear projection `P : H →L[ℝ] H`
     satisfying `IsSelfAdjointIdempotentProjection P` (`P (P x) = P x` and `⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ`):
     - **Orthogonal Complement Decomposition**: `⟪P k, k - P k⟫_ℝ = 0`.
     - **Pythagorean KV Reconstruction Identity**: `‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2`,
       `‖P k‖ ^ 2 ≤ ‖k‖ ^ 2`, and `‖k - P k‖ ^ 2 = 0 ↔ P k = k`.
     - **Attention Logit Error Cauchy–Schwarz Bound**:
       `|⟪q, k⟫_ℝ - ⟪q, P k⟫_ℝ| = |⟪q - P q, k - P k⟫_ℝ|` and
       `|⟪q, k⟫_ℝ - ⟪q, P k⟫_ℝ| ≤ ‖q - P q‖ * ‖k - P k‖`.
     - **Zero-Distortion Latent Attention Logit Preservation**:
       `(P q = q → ⟪q, P k⟫_ℝ = ⟪q, k⟫_ℝ) ∧ (P k = k → ⟪q, P k⟫_ℝ = ⟪q, k⟫_ℝ) ∧ ⟪P q, P k⟫_ℝ = ⟪P q, k⟫_ℝ`.

2. **Part 2: Finite-Dimensional Rank-`r` Orthonormal Latent Dictionary & Truncation Error
   (`fullKeyEnergy`, `latentProjectedEnergy`, `residualTailEnergy`,
   `mla_spectral_tail_truncation_conservation`)**:
   - For spectral coordinates `coeff : Fin d_full → ℝ` and a latent subset `S : Finset (Fin d_full)`:
     - `latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff`,
     - `0 ≤ residualTailEnergy S coeff`,
     - `latentProjectedEnergy S coeff ≤ fullKeyEnergy coeff`,
     - `residualTailEnergy S coeff = 0 ↔ ∀ i ∈ Finset.univ \ S, coeff i = 0`.

3. **Part 3: Exact Pointwise & Total-Variation Distribution-Level Lossless Speculative Decoding
   (`IsTokenPMF`, `speculativeAcceptedMass`, `speculativeResidualDeficit`,
   `speculativeAcceptanceRate`, `speculativeRejectionRate`, `totalVariationDistance`,
   `speculativeEmittedPMF`, `distribution_level_lossless_speculative_sampling_theorem`)**:
   - Over any finite vocabulary `V` (`[Fintype V] [DecidableEq V]`):
     - **Pointwise Exact Target Distribution Recovery**: `speculativeEmittedPMF p_target p_draft x = p_target x`.
     - **Pointwise Non-Negativity**: `0 ≤ speculativeAcceptedMass p_target p_draft x` and
       `0 ≤ speculativeResidualDeficit p_target p_draft x`.
     - **Conservation of Acceptance & Rejection Rates**:
       `speculativeAcceptanceRate p_target p_draft + speculativeRejectionRate p_target p_draft = 1`
       and `IsTokenPMF V (speculativeEmittedPMF p_target p_draft)`.
     - **Exact Total Variation Identity (`1 - α = TV(p_target, p_draft)`)**:
       `2 * speculativeAcceptedMass p_target p_draft x = p_target x + p_draft x - |p_target x - p_draft x|`,
       `speculativeAcceptanceRate p_target p_draft = 1 - totalVariationDistance p_target p_draft`, and
       `speculativeRejectionRate p_target p_draft = totalVariationDistance p_target p_draft`.
     - **Zero-TV Distance Implies 100% Acceptance**:
       `totalVariationDistance p_target p_target = 0` and
       `speculativeAcceptanceRate p_target p_target = 1`.

4. **Part 4: Grand Hilbert MLA & Distribution-Level Speculative Decoding Synthesis
   (`hilbert_mla_and_distribution_speculative_grand_theorem`)**:
   - Unites Parts 1–3 with `lossless_speculative_decoding_speedup_iff` and
     `mla_low_rank_kv_cache_roofline_speedup` from `OpenTheory.LongContextAndFastInference`.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace OpenTheory.HilbertMLAAndDistributionSpeculative

open OpenTheory
open OpenTheory.FastestTrainingAndRoofline
open OpenTheory.LongContextAndFastInference

/-! ## Part 1: Hilbert-Space Multi-Head Latent Attention (MLA) Orthogonal Projection & Exact Attention Logit Preservation -/

/-- **Self-Adjoint Idempotent Orthogonal Projection (`IsSelfAdjointIdempotentProjection`)**:
A continuous linear operator `P : H →L[ℝ] H` on a real inner product space `H` is an orthogonal
latent-subspace projection if it is idempotent (`P (P x) = P x`) and self-adjoint
(`⟪P x, y⟫ = ⟪x, P y⟫`). -/
structure IsSelfAdjointIdempotentProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H →L[ℝ] H) : Prop where
  idempotent : ∀ x : H, P (P x) = P x
  self_adjoint : ∀ x y : H, ⟪P x, y⟫ = ⟪x, P y⟫

/-- Applying a self-adjoint idempotent projection `P` to the residual `k - P k` yields zero:
`P (k - P k) = 0`. -/
theorem IsSelfAdjointIdempotentProjection.map_sub_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (k : H) :
    P (k - P k) = 0 := by
  rw [map_sub, hP.idempotent k, sub_self]

/-- **Orthogonal Complement Decomposition (`IsSelfAdjointIdempotentProjection.inner_proj_sub_self`)**:
For any `k : H`, the latent projection `P k` and the residual `k - P k` are orthogonal:
`⟪P k, k - P k⟫ = 0`. -/
theorem IsSelfAdjointIdempotentProjection.inner_proj_sub_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (k : H) :
    ⟪P k, k - P k⟫ = 0 := by
  rw [hP.self_adjoint k (k - P k), hP.map_sub_self k, inner_zero_right]

/-- For any `q k : H`, the projected query `P q` is orthogonal to the key residual `k - P k`:
`⟪P q, k - P k⟫ = 0`. -/
theorem IsSelfAdjointIdempotentProjection.inner_proj_left_sub_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (q k : H) :
    ⟪P q, k - P k⟫ = 0 := by
  rw [hP.self_adjoint q (k - P k), hP.map_sub_self k, inner_zero_right]

/-- **Pythagorean KV Reconstruction Identity (`IsSelfAdjointIdempotentProjection.norm_sq_eq_add_norm_sq`)**:
For any `k : H`, `‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2`. -/
theorem IsSelfAdjointIdempotentProjection.norm_sq_eq_add_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (k : H) :
    ‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2 := by
  have hk : k = P k + (k - P k) := (add_sub_cancel (P k) k).symm
  calc
    ‖k‖ ^ 2 = ‖P k + (k - P k)‖ ^ 2 := by rw [← hk]
    _ = ‖P k‖ ^ 2 + 2 * ⟪P k, k - P k⟫ + ‖k - P k‖ ^ 2 := norm_add_sq_real (P k) (k - P k)
    _ = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2 := by
      rw [hP.inner_proj_sub_self k]
      ring

/-- **Theorem 1: Hilbert-Space MLA Orthogonal Projection Pythagorean & Attention Logit Exactness
(`hilbert_mla_projection_pythagorean_and_logit_exactness`)**:
Given a continuous linear operator `P : H →L[ℝ] H` satisfying `hP : IsSelfAdjointIdempotentProjection P`:
1. **Orthogonal Complement Decomposition**:
   For every `k : H`, `⟪P k, k - P k⟫ = 0`.
2. **Pythagorean KV Reconstruction Identity**:
   For every `k : H`, `‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2`, `‖P k‖ ^ 2 ≤ ‖k‖ ^ 2`, and
   `‖k - P k‖ ^ 2 = 0 ↔ P k = k`.
3. **Attention Logit Error Cauchy–Schwarz Bound**:
   For any query vector `q : H` and key vector `k : H`,
   `|⟪q, k⟫ - ⟪q, P k⟫| = |⟪q - P q, k - P k⟫|` and
   `|⟪q, k⟫ - ⟪q, P k⟫| ≤ ‖q - P q‖ * ‖k - P k‖`.
4. **Zero-Distortion Latent Attention Logit Preservation**:
   `(P q = q → ⟪q, P k⟫ = ⟪q, k⟫) ∧ (P k = k → ⟪q, P k⟫ = ⟪q, k⟫) ∧ ⟪P q, P k⟫ = ⟪P q, k⟫`. -/
theorem hilbert_mla_projection_pythagorean_and_logit_exactness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (q k : H) :
    ⟪P k, k - P k⟫ = 0 ∧
    (‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2 ∧
      ‖P k‖ ^ 2 ≤ ‖k‖ ^ 2 ∧
      (‖k - P k‖ ^ 2 = 0 ↔ P k = k)) ∧
    (|⟪q, k⟫ - ⟪q, P k⟫| = |⟪q - P q, k - P k⟫| ∧
      |⟪q, k⟫ - ⟪q, P k⟫| ≤ ‖q - P q‖ * ‖k - P k‖) ∧
    ((P q = q → ⟪q, P k⟫ = ⟪q, k⟫) ∧
      (P k = k → ⟪q, P k⟫ = ⟪q, k⟫) ∧
      ⟪P q, P k⟫ = ⟪P q, k⟫) := by
  have horth : ⟪P k, k - P k⟫ = 0 := hP.inner_proj_sub_self k
  have hpyth : ‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2 := hP.norm_sq_eq_add_norm_sq k
  have hle : ‖P k‖ ^ 2 ≤ ‖k‖ ^ 2 := by
    have hnonneg : 0 ≤ ‖k - P k‖ ^ 2 := sq_nonneg ‖k - P k‖
    linarith
  have hzero_iff : ‖k - P k‖ ^ 2 = 0 ↔ P k = k := by
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm]
  have hlogit_diff : ⟪q, k⟫ - ⟪q, P k⟫ = ⟪q - P q, k - P k⟫ := by
    calc
      ⟪q, k⟫ - ⟪q, P k⟫ = ⟪q, k - P k⟫ := (inner_sub_right q k (P k)).symm
      _ = ⟪q, k - P k⟫ - ⟪P q, k - P k⟫ := by
        rw [hP.inner_proj_left_sub_self q k, sub_zero]
      _ = ⟪q - P q, k - P k⟫ := (inner_sub_left q (P q) (k - P k)).symm
  have habs_eq : |⟪q, k⟫ - ⟪q, P k⟫| = |⟪q - P q, k - P k⟫| := by
    rw [hlogit_diff]
  have habs_le : |⟪q, k⟫ - ⟪q, P k⟫| ≤ ‖q - P q‖ * ‖k - P k‖ := by
    rw [habs_eq]
    exact abs_real_inner_le_norm (q - P q) (k - P k)
  have h_pq_pk : ⟪P q, P k⟫ = ⟪P q, k⟫ := by
    rw [← hP.self_adjoint (P q) k, hP.idempotent q]
  refine ⟨horth, ⟨hpyth, hle, hzero_iff⟩, ⟨habs_eq, habs_le⟩, ⟨?_, ?_, h_pq_pk⟩⟩
  · intro hpq
    calc
      ⟪q, P k⟫ = ⟪P q, P k⟫ := by rw [hpq]
      _ = ⟪P q, k⟫ := h_pq_pk
      _ = ⟪q, k⟫ := by rw [hpq]
  · intro hpk
    rw [hpk]

/-! ## Part 2: Finite-Dimensional Rank-`r` Orthonormal Latent Dictionary & Truncation Error -/

/-- **Full Uncompressed Key Spectral Energy (`fullKeyEnergy`)**:
Total squared spectral coordinate energy `∑ i : Fin d_full, (coeff i) ^ 2` across all `d_full`
orthonormal basis directions. -/
def fullKeyEnergy {d_full : ℕ} (coeff : Fin d_full → ℝ) : ℝ :=
  ∑ i : Fin d_full, (coeff i) ^ 2

/-- **Latent-Projected Key Spectral Energy (`latentProjectedEnergy`)**:
Squared coordinate energy `∑ i ∈ S, (coeff i) ^ 2` captured by the selected rank-`r` latent subset
`S : Finset (Fin d_full)`. -/
def latentProjectedEnergy {d_full : ℕ} (S : Finset (Fin d_full)) (coeff : Fin d_full → ℝ) : ℝ :=
  ∑ i ∈ S, (coeff i) ^ 2

/-- **Residual Tail Truncation Energy (`residualTailEnergy`)**:
Discarded tail energy `∑ i ∈ Finset.univ \ S, (coeff i) ^ 2` outside the latent subset `S`. -/
def residualTailEnergy {d_full : ℕ} (S : Finset (Fin d_full)) (coeff : Fin d_full → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ \ S, (coeff i) ^ 2

/-- **Theorem 2: Spectral Tail Truncation & Energy Conservation Law
(`mla_spectral_tail_truncation_conservation`)**:
For any full dimension `d_full : ℕ`, coordinate vector `coeff : Fin d_full → ℝ`, and latent subset
`S : Finset (Fin d_full)`:
1. **Exact Spectral Energy Conservation**:
   `latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff`.
2. **Non-Negativity of Residual Tail Energy**:
   `0 ≤ residualTailEnergy S coeff`.
3. **Energy Monotonicity under Latent Projection**:
   `latentProjectedEnergy S coeff ≤ fullKeyEnergy coeff`.
4. **Exact Zero-Truncation Criterion**:
   `residualTailEnergy S coeff = 0 ↔ ∀ i ∈ Finset.univ \ S, coeff i = 0`. -/
theorem mla_spectral_tail_truncation_conservation
    {d_full : ℕ} (S : Finset (Fin d_full)) (coeff : Fin d_full → ℝ) :
    latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff ∧
    0 ≤ residualTailEnergy S coeff ∧
    latentProjectedEnergy S coeff ≤ fullKeyEnergy coeff ∧
    (residualTailEnergy S coeff = 0 ↔ ∀ i ∈ Finset.univ \ S, coeff i = 0) := by
  have hcons : latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff := by
    unfold latentProjectedEnergy residualTailEnergy fullKeyEnergy
    have hsub : S ⊆ Finset.univ := Finset.subset_univ S
    rw [add_comm, Finset.sum_sdiff hsub]
  have hnonneg : 0 ≤ residualTailEnergy S coeff := by
    unfold residualTailEnergy
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (coeff i))
  have hle : latentProjectedEnergy S coeff ≤ fullKeyEnergy coeff := by
    linarith
  have hzero_iff : residualTailEnergy S coeff = 0 ↔ ∀ i ∈ Finset.univ \ S, coeff i = 0 := by
    unfold residualTailEnergy
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (coeff i))]
    constructor
    · intro h i hi
      exact sq_eq_zero_iff.mp (h i hi)
    · intro h i hi
      exact sq_eq_zero_iff.mpr (h i hi)
  exact ⟨hcons, hnonneg, hle, hzero_iff⟩

/-! ## Part 3: Exact Pointwise & Total-Variation Distribution-Level Lossless Speculative Decoding -/

/-- **Finite-Vocabulary Token Probability Mass Function (`IsTokenPMF`)**:
A function `p : V → ℝ` on a finite token vocabulary `V` is a valid probability mass function if it
is pointwise non-negative (`∀ x, 0 ≤ p x`) and sums to one (`∑ x : V, p x = 1`). -/
structure IsTokenPMF (V : Type*) [Fintype V] (p : V → ℝ) : Prop where
  nonneg : ∀ x : V, 0 ≤ p x
  sum_eq_one : ∑ x : V, p x = 1

/-- **Speculative Accepted Mass at Token `x` (`speculativeAcceptedMass`)**:
In speculative sampling (Leviathan et al. 2023 / Chen et al. 2023), a draft token `x ~ p_draft` is
accepted with probability `min(1, p_target(x) / p_draft(x))`, yielding unconditional accepted mass
`p_draft(x) * min(1, p_target(x) / p_draft(x)) = min (p_draft x) (p_target x)`. -/
def speculativeAcceptedMass {V : Type*} (p_target p_draft : V → ℝ) (x : V) : ℝ :=
  min (p_draft x) (p_target x)

/-- **Speculative Residual (Rejected) Deficit Mass at Token `x` (`speculativeResidualDeficit`)**:
Unnormalized residual probability mass `max 0 (p_target x - p_draft x)` allocated to token `x`
during the target resampling step upon draft rejection. -/
def speculativeResidualDeficit {V : Type*} (p_target p_draft : V → ℝ) (x : V) : ℝ :=
  max 0 (p_target x - p_draft x)

/-- **Total Single-Step Speculative Acceptance Rate (`speculativeAcceptanceRate`)**:
Total probability `α = ∑ x : V, min (p_draft x) (p_target x)` that the draft token is accepted in a
single speculative verification step. -/
def speculativeAcceptanceRate {V : Type*} [Fintype V] (p_target p_draft : V → ℝ) : ℝ :=
  ∑ x : V, speculativeAcceptedMass p_target p_draft x

/-- **Total Single-Step Speculative Rejection Rate (`speculativeRejectionRate`)**:
Total probability `1 - α = ∑ x : V, max 0 (p_target x - p_draft x)` that the draft token is rejected
and replaced by a sample from the residual distribution. -/
def speculativeRejectionRate {V : Type*} [Fintype V] (p_target p_draft : V → ℝ) : ℝ :=
  ∑ x : V, speculativeResidualDeficit p_target p_draft x

/-- **Total Variation ($L^1$) Distance (`totalVariationDistance`)**:
The statistical total variation distance `(1 / 2) * ∑ x : V, |p_target x - p_draft x|` between the
target and draft token distributions. -/
def totalVariationDistance {V : Type*} [Fintype V] (p_target p_draft : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : V, |p_target x - p_draft x|

/-- **Emitted Speculative Decoding Token Probability (`speculativeEmittedPMF`)**:
Total marginal probability `speculativeAcceptedMass p_target p_draft x + speculativeResidualDeficit p_target p_draft x`
that speculative decoding emits token `x : V`. -/
def speculativeEmittedPMF {V : Type*} (p_target p_draft : V → ℝ) (x : V) : ℝ :=
  speculativeAcceptedMass p_target p_draft x + speculativeResidualDeficit p_target p_draft x

/-- **Pointwise Identity for Lossless Speculative Sampling (`speculativeEmittedPMF_eq_target`)**:
For every token `x : V`, `min (p_draft x) (p_target x) + max 0 (p_target x - p_draft x) = p_target x`. -/
theorem speculativeEmittedPMF_eq_target
    {V : Type*} (p_target p_draft : V → ℝ) (x : V) :
    speculativeEmittedPMF p_target p_draft x = p_target x := by
  unfold speculativeEmittedPMF speculativeAcceptedMass speculativeResidualDeficit
  rcases le_total (p_draft x) (p_target x) with hle | hge
  · have hsub : 0 ≤ p_target x - p_draft x := sub_nonneg.mpr hle
    rw [min_eq_left hle, max_eq_right hsub]
    ring
  · have hsub : p_target x - p_draft x ≤ 0 := sub_nonpos.mpr hge
    rw [min_eq_right hge, max_eq_left hsub, add_zero]

/-- **Pointwise Minimum–Absolute-Difference Identity (`two_mul_speculativeAcceptedMass_eq`)**:
For every token `x : V`,
`2 * speculativeAcceptedMass p_target p_draft x = p_target x + p_draft x - |p_target x - p_draft x|`. -/
theorem two_mul_speculativeAcceptedMass_eq
    {V : Type*} (p_target p_draft : V → ℝ) (x : V) :
    2 * speculativeAcceptedMass p_target p_draft x =
      p_target x + p_draft x - |p_target x - p_draft x| := by
  unfold speculativeAcceptedMass
  rcases le_total (p_draft x) (p_target x) with hle | hge
  · have hsub : 0 ≤ p_target x - p_draft x := sub_nonneg.mpr hle
    rw [min_eq_left hle, abs_of_nonneg hsub]
    ring
  · have hsub : p_target x - p_draft x ≤ 0 := sub_nonpos.mpr hge
    rw [min_eq_right hge, abs_of_nonpos hsub]
    ring

/-- **Theorem 3: Exact Pointwise & Total-Variation Distribution-Level Lossless Speculative Sampling
Theorem (`distribution_level_lossless_speculative_sampling_theorem`)**:
For any finite vocabulary `V` (`[Fintype V]`) and probability mass functions `p_target p_draft : V → ℝ`
satisfying `hp_t : IsTokenPMF V p_target` and `hp_d : IsTokenPMF V p_draft`:
1. **Pointwise Exact Target Distribution Recovery (Zero Distortion at Every Token `x : V`)**:
   `∀ x : V, speculativeEmittedPMF p_target p_draft x = p_target x`.
2. **Pointwise Non-Negativity of Accepted and Residual Masses**:
   `∀ x : V, 0 ≤ speculativeAcceptedMass p_target p_draft x ∧ 0 ≤ speculativeResidualDeficit p_target p_draft x`.
3. **Exact Conservation of Acceptance and Rejection Rates (`α + (1 - α) = 1`)**:
   `speculativeAcceptanceRate p_target p_draft + speculativeRejectionRate p_target p_draft = 1`
   and `IsTokenPMF V (speculativeEmittedPMF p_target p_draft)`.
4. **Exact Total Variation Identity (`α = 1 - TV(p_target, p_draft)` and `1 - α = TV(p_target, p_draft)`)**:
   `(∀ x : V, 2 * speculativeAcceptedMass p_target p_draft x = p_target x + p_draft x - |p_target x - p_draft x|)`
   and `speculativeAcceptanceRate p_target p_draft = 1 - totalVariationDistance p_target p_draft`
   and `speculativeRejectionRate p_target p_draft = totalVariationDistance p_target p_draft`.
5. **Zero-TV Distance Implies 100% Acceptance**:
   `totalVariationDistance p_target p_target = 0 ∧ speculativeAcceptanceRate p_target p_target = 1`. -/
theorem distribution_level_lossless_speculative_sampling_theorem
    {V : Type*} [Fintype V] {p_target p_draft : V → ℝ}
    (hp_t : IsTokenPMF V p_target) (hp_d : IsTokenPMF V p_draft) :
    (∀ x : V, speculativeEmittedPMF p_target p_draft x = p_target x) ∧
    (∀ x : V,
      0 ≤ speculativeAcceptedMass p_target p_draft x ∧
        0 ≤ speculativeResidualDeficit p_target p_draft x) ∧
    (speculativeAcceptanceRate p_target p_draft +
        speculativeRejectionRate p_target p_draft = 1 ∧
      IsTokenPMF V (speculativeEmittedPMF p_target p_draft)) ∧
    ((∀ x : V,
        2 * speculativeAcceptedMass p_target p_draft x =
          p_target x + p_draft x - |p_target x - p_draft x|) ∧
      speculativeAcceptanceRate p_target p_draft =
        1 - totalVariationDistance p_target p_draft ∧
      speculativeRejectionRate p_target p_draft =
        totalVariationDistance p_target p_draft) ∧
    (totalVariationDistance p_target p_target = 0 ∧
      speculativeAcceptanceRate p_target p_target = 1) := by
  have hpointwise : ∀ x : V, speculativeEmittedPMF p_target p_draft x = p_target x :=
    speculativeEmittedPMF_eq_target p_target p_draft
  have hnonneg : ∀ x : V,
      0 ≤ speculativeAcceptedMass p_target p_draft x ∧
        0 ≤ speculativeResidualDeficit p_target p_draft x := by
    intro x
    exact ⟨le_min (hp_d.nonneg x) (hp_t.nonneg x), le_max_left 0 (p_target x - p_draft x)⟩
  have hcons :
      speculativeAcceptanceRate p_target p_draft +
        speculativeRejectionRate p_target p_draft = 1 := by
    unfold speculativeAcceptanceRate speculativeRejectionRate
    rw [← Finset.sum_add_distrib]
    have hsum_eq :
        (∑ x : V, (speculativeAcceptedMass p_target p_draft x +
          speculativeResidualDeficit p_target p_draft x)) =
          ∑ x : V, p_target x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact speculativeEmittedPMF_eq_target p_target p_draft x
    rw [hsum_eq, hp_t.sum_eq_one]
  have hpmf_emitted : IsTokenPMF V (speculativeEmittedPMF p_target p_draft) := by
    refine ⟨?_, ?_⟩
    · intro x
      rw [hpointwise x]
      exact hp_t.nonneg x
    · have hsum : (∑ x : V, speculativeEmittedPMF p_target p_draft x) = ∑ x : V, p_target x :=
        Finset.sum_congr rfl (fun x _ => hpointwise x)
      rw [hsum, hp_t.sum_eq_one]
  have h2min : ∀ x : V,
      2 * speculativeAcceptedMass p_target p_draft x =
        p_target x + p_draft x - |p_target x - p_draft x| :=
    two_mul_speculativeAcceptedMass_eq p_target p_draft
  have hacc_tv :
      speculativeAcceptanceRate p_target p_draft =
        1 - totalVariationDistance p_target p_draft := by
    have hsum2 :
        2 * speculativeAcceptanceRate p_target p_draft =
          (∑ x : V, p_target x) + (∑ x : V, p_draft x) -
            ∑ x : V, |p_target x - p_draft x| := by
      unfold speculativeAcceptanceRate
      rw [Finset.mul_sum]
      have hcongr :
          (∑ x : V, 2 * speculativeAcceptedMass p_target p_draft x) =
            ∑ x : V, (p_target x + p_draft x - |p_target x - p_draft x|) :=
        Finset.sum_congr rfl (fun x _ => h2min x)
      rw [hcongr, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hp_t.sum_eq_one, hp_d.sum_eq_one] at hsum2
    unfold totalVariationDistance
    linarith
  have hrej_tv :
      speculativeRejectionRate p_target p_draft =
        totalVariationDistance p_target p_draft := by
    linarith
  have htv_self : totalVariationDistance p_target p_target = 0 := by
    unfold totalVariationDistance
    simp
  have hacc_self : speculativeAcceptanceRate p_target p_target = 1 := by
    unfold speculativeAcceptanceRate speculativeAcceptedMass
    simp [hp_t.sum_eq_one]
  exact ⟨hpointwise, hnonneg, ⟨hcons, hpmf_emitted⟩, ⟨h2min, hacc_tv, hrej_tv⟩,
    ⟨htv_self, hacc_self⟩⟩

/-! ## Part 4: Grand Hilbert MLA & Distribution-Level Speculative Decoding Synthesis -/

/-- **Theorem 4: Grand Hilbert MLA & Distribution-Level Lossless Speculative Decoding Synthesis
(`hilbert_mla_and_distribution_speculative_grand_theorem`)**:
Unites:
1. **Hilbert-Space MLA Orthogonal Projection Pythagorean & Attention Logit Exactness**:
   `‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2` and `|⟪q, k⟫ - ⟪q, P k⟫| ≤ ‖q - P q‖ * ‖k - P k‖`.
2. **Spectral Tail Truncation Energy Conservation**:
   `latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff`.
3. **Distribution-Level Lossless Speculative Sampling & Exact Total-Variation Acceptance Law**:
   `speculativeEmittedPMF p_target p_draft x = p_target x`,
   `speculativeAcceptanceRate p_target p_draft = 1 - totalVariationDistance p_target p_draft`, and
   `speculativeRejectionRate p_target p_draft = totalVariationDistance p_target p_draft`.
4. **Hardware-Roofline Latency Speedup & Lossless Speculative Decoding Acceleration Law**:
   `speculativeAmortizedPerTokenLatency K_draft t_draft t_verify E_accepted < standardAutoregressivePerTokenLatency t_verify ↔ (K_draft : ℝ) * t_draft < E_accepted * t_verify`. -/
theorem hilbert_mla_and_distribution_speculative_grand_theorem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : H →L[ℝ] H} (hP : IsSelfAdjointIdempotentProjection P) (q k : H)
    {d_full : ℕ} (S : Finset (Fin d_full)) (coeff : Fin d_full → ℝ)
    {V : Type*} [Fintype V] {p_target p_draft : V → ℝ}
    (hp_t : IsTokenPMF V p_target) (hp_d : IsTokenPMF V p_draft)
    {K_draft : ℕ} {t_draft t_verify E_accepted : ℝ}
    (hK : 1 ≤ K_draft) (ht_draft : 0 < t_draft) (ht_verify : 0 < t_verify)
    (hE : 0 < E_accepted) :
    (‖k‖ ^ 2 = ‖P k‖ ^ 2 + ‖k - P k‖ ^ 2 ∧
      |⟪q, k⟫ - ⟪q, P k⟫| ≤ ‖q - P q‖ * ‖k - P k‖ ∧
      ⟪P q, P k⟫ = ⟪P q, k⟫) ∧
    (latentProjectedEnergy S coeff + residualTailEnergy S coeff = fullKeyEnergy coeff ∧
      latentProjectedEnergy S coeff ≤ fullKeyEnergy coeff) ∧
    ((∀ x : V, speculativeEmittedPMF p_target p_draft x = p_target x) ∧
      speculativeAcceptanceRate p_target p_draft =
        1 - totalVariationDistance p_target p_draft ∧
      speculativeRejectionRate p_target p_draft =
        totalVariationDistance p_target p_draft) ∧
    ((speculativeAmortizedPerTokenLatency K_draft t_draft t_verify E_accepted <
        standardAutoregressivePerTokenLatency t_verify ↔
      (K_draft : ℝ) * t_draft < E_accepted * t_verify) ∧
      standardAutoregressivePerTokenLatency t_verify /
          speculativeAmortizedPerTokenLatency K_draft t_draft t_verify E_accepted =
        (1 + E_accepted) / (1 + (K_draft : ℝ) * (t_draft / t_verify))) := by
  have h1 := hilbert_mla_projection_pythagorean_and_logit_exactness hP q k
  have h2 := mla_spectral_tail_truncation_conservation S coeff
  have h3 := distribution_level_lossless_speculative_sampling_theorem hp_t hp_d
  have h4 := lossless_speculative_decoding_speedup_iff hK ht_draft ht_verify hE
  exact ⟨⟨h1.2.1.1, h1.2.2.1.2, h1.2.2.2.2.2⟩, ⟨h2.1, h2.2.2.1⟩,
    ⟨h3.1, h3.2.2.2.1.2.1, h3.2.2.2.1.2.2⟩, ⟨h4.1, h4.2.1⟩⟩

end OpenTheory.HilbertMLAAndDistributionSpeculative
