import Hironaka.Resolution.Standard.Analytic

/-!
# Resolution of singularities in the form singular learning theory uses

Watanabe's theory of Bayesian learning for singular models starts from resolution of
singularities: a proper analytic change of variables after which the population loss `K` and the
Jacobian determinant are, near every point, monomials up to analytic units [Wat09, Theorem 2.3].
That theorem is Resolution's formalization of Hironaka's theorem in its real-analytic form
(`exists_proper_analytic_monomialization`, `resolutionorg/hironaka` tag `v4.34.0`, a pinned Lake
dependency, so its proof is checked in this build).

Integral estimates use the monomial form only through two-sided bounds:

* `IsMonomialAt.exists_abs_bounds`: a monomial times a unit is, near the point, between two
  positive multiples of the absolute value of the monomial;
* `exists_resolution_monomial_bounds`: for `K` analytic on `U ⊆ ℝⁿ` and not identically zero near
  any point, there is a proper analytic `π : M → U`, bijective over `{K ≠ 0}`, such that near every
  point of `M`, `|K ∘ π|` and the Jacobian determinant are comparable to monomials in the chart
  coordinates; and the preimage of every compact set, such as the support of a prior, is covered
  by finitely many such neighbourhoods. For `K ≥ 0`, `|K ∘ π| = K ∘ π`.

On each neighbourhood the zeta integral `∫ K^{-s} φ` is then comparable to the normal-crossing
integrals of `formal/core/LearningTheory/Singular/NormalCrossing.lean`.
-/

open Filter Topology Set
open scoped Manifold ContDiff

namespace OpenTheory.Singular

/-- The monomial `∏ yᵢ^{αᵢ}` in the coordinates `y` of the chart at `p`, evaluated at `q`. -/
noncomputable def chartMonomial (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) (α : Fin n → ℕ) (q : M) : ℝ :=
  ∏ i, extChartAt (𝓡 n) p q i ^ α i

/-- **Two-sided monomial bounds.** Near `p`, a monomial up to a unit lies between two positive
multiples of the absolute value of the monomial. -/
theorem IsMonomialAt.exists_abs_bounds {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {g : M → ℝ} {p : M} (hg : IsMonomialAt n g p) :
    ∃ (α : Fin n → ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧ ∀ᶠ q in 𝓝 p,
      c * |chartMonomial n p α q| ≤ |g q| ∧ |g q| ≤ C * |chartMonomial n p α q| := by
  obtain ⟨α, u, hu, hup, hgu⟩ := hg
  have hcont : ContinuousAt (fun q => |u q|) p := hu.continuousAt.abs
  have h0 : 0 < |u p| := abs_pos.2 hup
  refine ⟨α, |u p| / 2, 2 * |u p|, by positivity, by positivity, ?_⟩
  have hlo : ∀ᶠ q in 𝓝 p, |u p| / 2 < |u q| := hcont.eventually (lt_mem_nhds (by linarith))
  have hhi : ∀ᶠ q in 𝓝 p, |u q| < 2 * |u p| := hcont.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hgu, hlo, hhi] with q hq hl hh
  rw [hq, abs_mul, chartMonomial]
  have := abs_nonneg (∏ i, extChartAt (𝓡 n) p q i ^ α i)
  constructor <;> nlinarith

/-- The bounds of `exists_resolution_monomial_bounds` at `q`, for the data chosen at `p`: `|g₁ q|`
and `|g₂ q|` are within the factors `c, C` of the monomials with exponents `α, β` in the chart at
`p`. -/
def MonomialBounds (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (g₁ g₂ : M → ℝ) (p : M) (α β : Fin n → ℕ)
    (c C : ℝ) (q : M) : Prop :=
  (c * |chartMonomial n p α q| ≤ |g₁ q| ∧ |g₁ q| ≤ C * |chartMonomial n p α q|) ∧
    (c * |chartMonomial n p β q| ≤ |g₂ q| ∧ |g₂ q| ≤ C * |chartMonomial n p β q|)

/-- **Resolution of singularities, in the form used for Bayesian integrals.** Let `K` be
real-analytic on an open `U ⊆ ℝⁿ` and not identically zero near any point. There is a proper
real-analytic map `π : M → U` from an `n`-dimensional real-analytic manifold, bijective over
`{K ≠ 0}`, and for every `p : M` exponents `α p, β p` and constants `0 < c p, C p`, such that near
`p`, `|K ∘ π|` and the Jacobian determinant of `π` (in the chart at `p`) lie within the factors
`c p, C p` of the monomials `y^{α p}` and `y^{β p}` in the chart coordinates `y`. The preimage of
every compact `S ⊆ U` is covered by finitely many of these neighbourhoods.

Derived from `exists_proper_analytic_monomialization` (Atiyah's resolution theorem with the
Jacobian clause of Bierstone–Milman), proved in `resolutionorg/hironaka`. -/
theorem exists_resolution_monomial_bounds {n : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    {K : EuclideanSpace ℝ (Fin n) → ℝ} (hK : AnalyticOnNhd ℝ K U)
    (hK₀ : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, K y ≠ 0) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (π : M → U),
      IsManifold (𝓡 n) ω M ∧ T2Space M ∧ SecondCountableTopology M ∧
      ContMDiff (𝓡 n) (𝓡 n) ω π ∧ IsProperMap π ∧
      Set.BijOn π (π ⁻¹' {x | K x ≠ 0}) {x | K x ≠ 0} ∧
      ∃ (α β : M → Fin n → ℕ) (c C : M → ℝ),
        let J : M → M → ℝ := fun p q =>
          (fderiv ℝ ((↑) ∘ π ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p q)).det
        (∀ p, 0 < c p ∧ 0 < C p ∧ ∀ᶠ q in 𝓝 p,
          MonomialBounds n (fun q => K (π q)) (J p) p (α p) (β p) (c p) (C p) q) ∧
        ∀ S : Set U, IsCompact S → ∃ t : Finset M, π ⁻¹' S ⊆
          ⋃ p ∈ t, {q | MonomialBounds n (fun q => K (π q)) (J p) p (α p) (β p) (c p) (C p) q} := by
  obtain ⟨M, _, _, π, hman, hT2, hsc, hπ, hprop, -, hbij, hmono⟩ :=
    exists_proper_analytic_monomialization.{0} U hK hK₀
  refine ⟨M, ‹_›, ‹_›, π, hman, hT2, hsc, hπ, hprop, hbij, ?_⟩
  set J : M → M → ℝ := fun p q =>
    (fderiv ℝ ((↑) ∘ π ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p q)).det
  have hloc : ∀ p : M, ∃ (αβ : (Fin n → ℕ) × (Fin n → ℕ)) (cC : ℝ × ℝ), 0 < cC.1 ∧ 0 < cC.2 ∧
      ∀ᶠ q in 𝓝 p, MonomialBounds n (fun q => K (π q)) (J p) p αβ.1 αβ.2 cC.1 cC.2 q := by
    intro p
    obtain ⟨α, c₁, C₁, hc₁, hC₁, h₁⟩ := IsMonomialAt.exists_abs_bounds (hmono p).1
    obtain ⟨β, c₂, C₂, hc₂, hC₂, h₂⟩ := IsMonomialAt.exists_abs_bounds (hmono p).2
    refine ⟨(α, β), (min c₁ c₂, max C₁ C₂), lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, ?_⟩
    filter_upwards [h₁, h₂] with q hq₁ hq₂
    have m₁ := abs_nonneg (chartMonomial n p α q)
    have m₂ := abs_nonneg (chartMonomial n p β q)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) m₁).trans hq₁.1
    · exact hq₁.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) m₁)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) m₂).trans hq₂.1
    · exact hq₂.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) m₂)
  choose αβ cC hc hC hev using hloc
  refine ⟨fun p => (αβ p).1, fun p => (αβ p).2, fun p => (cC p).1, fun p => (cC p).2,
    fun p => ⟨hc p, hC p, hev p⟩, fun S hS => ?_⟩
  obtain ⟨t, -, ht⟩ := (hprop.isCompact_preimage hS).elim_nhds_subcover _ fun p _ => hev p
  exact ⟨t, ht⟩

end OpenTheory.Singular
