import Theory.Training.Singular.Resolution
import Theory.Training.Singular.MonomialBox

/-!
# Every analytic model has a rational learning coefficient

Watanabe's foundational theorem of singular learning theory, in its deterministic form: for a
real-analytic loss `K ≥ 0` on an open `U ⊆ ℝⁿ`, not identically zero near any point, and a
continuous prior `φ` with compact support in `U` that is positive at the zeros of `K` in its
support, there is a positive rational `λ` with

  `∫ K^{-s} φ < ∞  ⟺  s < λ`     (`s ≥ 0`),

the real log canonical threshold (`exists_isRLCT`).

Proof. Resolve `K` (`exists_proper_analytic_monomialization`, Resolution's formalization of
Hironaka's theorem). Around every point `p` of the resolved manifold choose a coordinate box in
the chart at `p` on which `K ∘ ρ` and the Jacobian are comparable to monomials `y^α`, `y^β`
(`LocalBox`). Properness of `ρ` makes the preimage of the support of `φ` compact, so finitely
many boxes cover it. By the change of variables formula each piece of the zeta integral is
comparable to `∫_B ∏ |yᵢ|^{βᵢ - s αᵢ}`, finite iff `s < (βᵢ + 1)/αᵢ` at every coordinate where the
centre vanishes (`lintegral_box_monomial_lt_top_iff`). `λ` is the least of these finitely many
rationals. The zero set of `K` is null, being covered by images of coordinate hyperplanes.
-/

noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped ENNReal Manifold ContDiff

namespace OpenTheory.Singular

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

/-- The resolution map read in the chart at `p`: `y ↦ ρ (chart⁻¹ y)` in `ℝⁿ`. -/
def chartMap (ρ : M → U) (p : M) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  (↑) ∘ ρ ∘ (extChartAt (𝓡 n) p).symm

theorem chartMap_extChartAt (ρ : M → U) {p q : M} (hq : q ∈ (extChartAt (𝓡 n) p).source) :
    chartMap ρ p (extChartAt (𝓡 n) p q) = ρ q := by
  simp only [chartMap, Function.comp_apply]
  rw [(extChartAt (𝓡 n) p).left_inv hq]

theorem differentiableAt_chartMap [IsManifold (𝓡 n) ω M] {ρ : M → U}
    (hρ : ContMDiff (𝓡 n) (𝓡 n) ω ρ) (p : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) : DifferentiableAt ℝ (chartMap ρ p) y := by
  have h1 : ContMDiffOn (𝓡 n) (𝓡 n) ω (chartMap ρ p) (extChartAt (𝓡 n) p).target :=
    (contMDiff_subtype_val.comp hρ).comp_contMDiffOn (contMDiffOn_extChartAt_symm p)
  exact ((contMDiffOn_iff_contDiffOn.1 h1).differentiableOn (by simp)).differentiableAt
    ((isOpen_extChartAt_target p).mem_nhds hy)

/-- A box in the chart at `p` on which `K ∘ ρ` and the Jacobian determinant of `ρ` are within
constant factors of the monomials `y^α` and `y^β`, every coordinate of the centre is `0` or
larger than the half-width, and the prior stays above half its value at `ρ p`. -/
structure LocalBox (ρ : M → U) (K φ : EuclideanSpace ℝ (Fin n) → ℝ) (p : M) where
  α : Fin n → ℕ
  β : Fin n → ℕ
  c : ℝ
  C : ℝ
  r : ℝ
  c_pos : 0 < c
  C_pos : 0 < C
  r_pos : 0 < r
  box_sub : box (extChartAt (𝓡 n) p p) r ⊆ (extChartAt (𝓡 n) p).target
  center : ∀ i, extChartAt (𝓡 n) p p i = 0 ∨ r < |extChartAt (𝓡 n) p p i|
  diff : ∀ y ∈ box (extChartAt (𝓡 n) p p) r, DifferentiableAt ℝ (chartMap ρ p) y
  K_lower : ∀ y ∈ box (extChartAt (𝓡 n) p p) r, c * |∏ i, y i ^ α i| ≤ |K (chartMap ρ p y)|
  K_upper : ∀ y ∈ box (extChartAt (𝓡 n) p p) r, |K (chartMap ρ p y)| ≤ C * |∏ i, y i ^ α i|
  J_lower : ∀ y ∈ box (extChartAt (𝓡 n) p p) r,
    c * |∏ i, y i ^ β i| ≤ |(fderiv ℝ (chartMap ρ p) y).det|
  J_upper : ∀ y ∈ box (extChartAt (𝓡 n) p p) r,
    |(fderiv ℝ (chartMap ρ p) y).det| ≤ C * |∏ i, y i ^ β i|
  φ_lower : 0 < φ (ρ p) → ∀ y ∈ box (extChartAt (𝓡 n) p p) r, φ (ρ p) / 2 ≤ φ (chartMap ρ p y)

theorem localBox_nonempty [IsManifold (𝓡 n) ω M] {ρ : M → U} (hρ : ContMDiff (𝓡 n) (𝓡 n) ω ρ)
    {K φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ) (p : M)
    (hK : IsMonomialAt n (fun q => K (ρ q)) p)
    (hJ : IsMonomialAt n (fun q =>
      (fderiv ℝ ((↑) ∘ ρ ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p q)).det) p) :
    Nonempty (LocalBox ρ K φ p) := by
  set e := extChartAt (𝓡 n) p with he
  obtain ⟨α, c₁, C₁, hc₁, hC₁, h₁⟩ := IsMonomialAt.exists_abs_bounds hK
  obtain ⟨β, c₂, C₂, hc₂, hC₂, h₂⟩ := IsMonomialAt.exists_abs_bounds hJ
  have hsymm : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have := continuousAt_extChartAt_symm (I := 𝓡 n) p
    rwa [ContinuousAt, extChartAt_to_inv] at this
  have hF : chartMap ρ p (e p) = ρ p := chartMap_extChartAt ρ (mem_extChartAt_source p)
  have hφev : ∀ᶠ y in 𝓝 (e p), 0 < φ (ρ p) → φ (ρ p) / 2 ≤ φ (chartMap ρ p y) := by
    by_cases hp : 0 < φ (ρ p)
    · have hcont : ContinuousAt (fun y => φ (chartMap ρ p y)) (e p) :=
        hφ.continuousAt.comp (differentiableAt_chartMap hρ p (mem_extChartAt_target p)).continuousAt
      have : ∀ᶠ y in 𝓝 (e p), φ (ρ p) / 2 < φ (chartMap ρ p y) := by
        refine hcont.eventually (lt_mem_nhds ?_)
        simp only [hF]
        linarith
      exact this.mono fun y hy _ => hy.le
    · exact Eventually.of_forall fun _ h => absurd h hp
  have hev : ∀ᶠ y in 𝓝 (e p), y ∈ e.target ∧
      (c₁ * |chartMonomial n p α (e.symm y)| ≤ |K (ρ (e.symm y))| ∧
        |K (ρ (e.symm y))| ≤ C₁ * |chartMonomial n p α (e.symm y)|) ∧
      (c₂ * |chartMonomial n p β (e.symm y)| ≤
          |(fderiv ℝ ((↑) ∘ ρ ∘ e.symm) (e (e.symm y))).det| ∧
        |(fderiv ℝ ((↑) ∘ ρ ∘ e.symm) (e (e.symm y))).det| ≤
          C₂ * |chartMonomial n p β (e.symm y)|) ∧
      (0 < φ (ρ p) → φ (ρ p) / 2 ≤ φ (chartMap ρ p y)) :=
    Filter.Eventually.and (show ∀ᶠ y in 𝓝 (e p), y ∈ e.target from extChartAt_target_mem_nhds p)
      ((hsymm.eventually h₁).and ((hsymm.eventually h₂).and hφev))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  -- the half-width
  have hr1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have hr2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε / (n + 1) :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / (n + 1))).filter_mono nhdsWithin_le_nhds
  have hr3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i, e p i = 0 ∨ r < |e p i| := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hci : e p i = 0
    · exact Eventually.of_forall fun _ => Or.inl hci
    · exact ((eventually_lt_nhds (abs_pos.2 hci)).filter_mono nhdsWithin_le_nhds).mono
        fun _ h => Or.inr h
  obtain ⟨r, hr0, hrε, hrc⟩ := (hr1.and (hr2.and hr3)).exists
  have hP : ∀ y ∈ box (e p) r, _ := fun y hy => hball (box_subset_ball (e p) hr0 hrε hy)
  have hinv : ∀ y ∈ box (e p) r, e (e.symm y) = y := fun y hy => e.right_inv (hP y hy).1
  have hmono : ∀ (γ : Fin n → ℕ) y, y ∈ box (e p) r →
      chartMonomial n p γ (e.symm y) = ∏ i, y i ^ γ i := fun γ y hy => by
    rw [chartMonomial, ← he, hinv y hy]
  refine ⟨⟨α, β, min c₁ c₂, max C₁ C₂, r, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, hr0,
    fun y hy => (hP y hy).1, hrc, fun y hy => differentiableAt_chartMap hρ p (hP y hy).1,
    ?_, ?_, ?_, ?_, fun h y hy => (hP y hy).2.2.2 h⟩⟩
  · intro y hy
    have h := (hP y hy).2.1.1
    rw [hmono α y hy] at h
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans h
  · intro y hy
    have h := (hP y hy).2.1.2
    rw [hmono α y hy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · intro y hy
    have h := (hP y hy).2.2.1.1
    rw [hmono β y hy, hinv y hy] at h
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)).trans h
  · intro y hy
    have h := (hP y hy).2.2.1.2
    rw [hmono β y hy, hinv y hy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
/-- A resolution map is onto: its range is closed (`ρ` is proper) and contains the dense set
`{K ≠ 0}`. -/
theorem surjective_of_resolution {ρ : M → U} {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hprop : IsProperMap ρ) (hbij : Set.BijOn ρ (ρ ⁻¹' {x | K x ≠ 0}) {x | K x ≠ 0})
    (hK₀ : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, K y ≠ 0) : Function.Surjective ρ := by
  have hsub : {x : U | K x ≠ 0} ⊆ range ρ := fun x hx =>
    let ⟨q, _, hq⟩ := hbij.surjOn hx
    ⟨q, hq⟩
  intro x
  have hx : x ∈ closure {x : U | K x ≠ 0} := by
    rw [mem_closure_iff_frequently]
    have h := hK₀ x x.2
    rw [← (U.isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq x] at h
    exact Filter.frequently_map.1 h
  have := closure_mono hsub hx
  rwa [hprop.isClosedMap.isClosed_range.closure_eq] at this

/-- `|y^β| |y^α|^{-s} = ∏ |yᵢ|^{βᵢ - s αᵢ}` when no coordinate vanishes. -/
theorem abs_monomial_mul_rpow {y : EuclideanSpace ℝ (Fin n)} (hy : ∀ i, y i ≠ 0)
    (α β : Fin n → ℕ) (s : ℝ) :
    |∏ i, y i ^ β i| * |∏ i, y i ^ α i| ^ (-s) = ∏ i, |y i| ^ ((β i : ℝ) - s * α i) := by
  have hpos : ∀ i, 0 < |y i| := fun i => abs_pos.2 (hy i)
  rw [Finset.abs_prod, Finset.abs_prod, ← Real.finsetProd_rpow _ _ fun i _ => abs_nonneg _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_pow, abs_pow, ← rpow_natCast, ← rpow_natCast, ← rpow_mul (hpos i).le,
    ← rpow_add (hpos i)]
  ring_nf

theorem abs_monomial_pos {y : EuclideanSpace ℝ (Fin n)} (hy : ∀ i, y i ≠ 0) (α : Fin n → ℕ) :
    0 < |∏ i, y i ^ α i| :=
  abs_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hy i))

theorem exists_coord_eq_zero_of_monomial {y : EuclideanSpace ℝ (Fin n)} {α : Fin n → ℕ} {c : ℝ}
    (hc : 0 < c) (h : c * |∏ i, y i ^ α i| ≤ 0) : ∃ i, y i = 0 ∧ α i ≠ 0 := by
  have h0 : ∏ i, y i ^ α i = 0 := abs_eq_zero.1 (le_antisymm
    (nonpos_of_mul_nonpos_right (by linarith) hc |>.trans le_rfl |> fun h' => by
      nlinarith [abs_nonneg (∏ i, y i ^ α i)]) (abs_nonneg _))
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h0
  exact ⟨i, eq_zero_of_pow_eq_zero hi, fun h => by simp [h] at hi⟩

/-- **The learning coefficient of an analytic model exists and is a positive rational.**
Let `K ≥ 0` be real-analytic on an open `U ⊆ ℝⁿ` and not identically zero near any point, and
let the prior `φ` be continuous with compact support in `U`, positive at every zero of `K` in its
support, with at least one such zero. Then for some positive rational `λ`, the zeta integral
`∫ K^{-s} φ` is finite exactly for `0 ≤ s < λ`. -/
theorem exists_isRLCT (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    {K : EuclideanSpace ℝ (Fin n) → ℝ} (hK : AnalyticOnNhd ℝ K U)
    (hK₀ : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, K y ≠ 0) (hKnn : ∀ x ∈ U, 0 ≤ K x)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hpos : ∀ x ∈ tsupport φ, K x = 0 → 0 < φ x)
    (hzero : ∃ x ∈ tsupport φ, K x = 0) :
    ∃ lam : ℚ, 0 < lam ∧ IsRLCT K φ volume lam := by
  classical
  obtain ⟨M, _, _, ρ, hman, -, -, hρ, hprop, -, hbij, hmono⟩ :=
    exists_proper_analytic_monomialization.{0} U hK hK₀
  have := hman
  have hsurj := surjective_of_resolution hprop hbij hK₀
  let B : ∀ p, LocalBox ρ K φ p := fun p =>
    (localBox_nonempty hρ hφ p (hmono p).1 (hmono p).2).some
  -- notation
  let e : M → PartialEquiv M (EuclideanSpace ℝ (Fin n)) := fun p => extChartAt (𝓡 n) p
  let bx : M → Set (EuclideanSpace ℝ (Fin n)) := fun p => box (e p p) (B p).r
  let F : M → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p => chartMap ρ p
  have hFU : ∀ p y, F p y ∈ U := fun p y => (ρ ((e p).symm y)).2
  have hKF : ∀ p y, 0 ≤ K (F p y) := fun p y => hKnn _ (hFU p y)
  -- the finite cover
  have hS : IsCompact ((↑) ⁻¹' tsupport φ : Set U) := by
    rw [Subtype.isCompact_iff]
    convert hφc.isCompact using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hφU h⟩, h, rfl⟩
  let V : M → Set M := fun p => (e p).source ∩ e p ⁻¹' bx p
  have hV : ∀ p, V p ∈ 𝓝 p := fun p =>
    (isOpen_extChartAt_preimage' p (isOpen_box _ _)).mem_nhds
      ⟨mem_extChartAt_source p, mem_box_self _ (B p).r_pos⟩
  obtain ⟨t, ht_mem, ht_cover⟩ :=
    (hprop.isCompact_preimage hS).elim_nhds_subcover V fun p _ => hV p
  have hcover : ∀ w ∈ tsupport φ, ∃ p ∈ t, ∃ y ∈ bx p, F p y = w := by
    intro w hw
    obtain ⟨q, hq⟩ := hsurj ⟨w, hφU hw⟩
    have hqS : q ∈ ρ ⁻¹' ((↑) ⁻¹' tsupport φ : Set U) := by simp [hq, hw]
    obtain ⟨p, hp, hqV⟩ := mem_iUnion₂.1 (ht_cover hqS)
    refine ⟨p, hp, e p q, hqV.2, ?_⟩
    show chartMap ρ p (extChartAt (𝓡 n) p q) = w
    rw [chartMap_extChartAt ρ hqV.1, hq]
  -- the threshold: least `(βᵢ + 1)/αᵢ` over vanishing centre coordinates with `αᵢ > 0`
  let T : Finset (M × Fin n) :=
    (t ×ˢ Finset.univ).filter fun pi => e pi.1 pi.1 pi.2 = 0 ∧ 0 < (B pi.1).α pi.2
  let val : M × Fin n → ℚ := fun pi => (((B pi.1).β pi.2 : ℚ) + 1) / (B pi.1).α pi.2
  have hTne : (T.image val).Nonempty := by
    obtain ⟨w, hw, hKw⟩ := hzero
    obtain ⟨p, hp, y, hy, hFy⟩ := hcover w hw
    have hle : (B p).c * |∏ i, y i ^ (B p).α i| ≤ 0 := by
      have := (B p).K_lower y hy
      simp only [F] at hFy
      rwa [hFy, hKw, abs_zero] at this
    obtain ⟨i, hyi, hαi⟩ := exists_coord_eq_zero_of_monomial (B p).c_pos hle
    have hci : e p p i = 0 := by
      rcases (B p).center i with h | h
      · exact h
      · have := hy i
        rw [hyi] at this
        exact absurd (abs_lt.2 ⟨by linarith [this.2], by linarith [this.1]⟩) (not_lt.2 h.le)
    exact ⟨val (p, i), Finset.mem_image_of_mem _
      (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp, Finset.mem_univ _⟩, hci, Nat.pos_of_ne_zero hαi⟩)⟩
  set lam : ℚ := (T.image val).min' hTne with hlam
  have hlam_le : ∀ pi ∈ T, lam ≤ val pi := fun pi hpi =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hpi)
  obtain ⟨pi₀, hpi₀, hval₀⟩ := Finset.mem_image.1 (Finset.min'_mem _ hTne)
  obtain ⟨p₀, i₀⟩ := pi₀
  have hT₀ := Finset.mem_filter.1 hpi₀
  have hlam_pos : 0 < lam := by
    rw [hlam, ← hval₀]
    have : (0 : ℚ) < (B p₀).α i₀ := by exact_mod_cast hT₀.2.2
    positivity
  refine ⟨lam, hlam_pos, fun s hs => ?_⟩
  -- the pieces of the integral
  let D : M → Set (EuclideanSpace ℝ (Fin n)) := fun p => bx p ∩ (fun y => K (F p y)) ⁻¹' {0}ᶜ
  have hDopen : ∀ p, IsOpen (D p) := fun p => by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_box _ _) isOpen_compl_singleton
    exact hK.continuousOn.comp (fun y hy => ((B p).diff y hy).continuousAt.continuousWithinAt)
      fun y _ => hFU p y
  have hinj : ∀ p, InjOn (F p) (D p) := by
    intro p y₁ hy₁ y₂ hy₂ heq
    have h := hbij.injOn (x₁ := (e p).symm y₁) (x₂ := (e p).symm y₂) hy₁.2 hy₂.2 (Subtype.ext heq)
    exact (e p).symm.injOn ((B p).box_sub hy₁.1) ((B p).box_sub hy₂.1) h
  let G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (K w) ^ (-s) * ENNReal.ofReal (φ w)
  have hcov : ∀ p, ∫⁻ w in F p '' D p, G w =
      ∫⁻ y in D p, ENNReal.ofReal |(fderiv ℝ (F p) y).det| * G (F p y) := fun p =>
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hDopen p).measurableSet
      (fun y hy => ((B p).diff y hy.1).hasFDerivAt.hasFDerivWithinAt) (hinj p) G
  let a : M → Fin n → ℝ := fun p i => ((B p).β i : ℝ) - s * (B p).α i
  -- a box point where `K ∘ F` vanishes has a zero coordinate
  have hzero_coord : ∀ p, ∀ y ∈ bx p, K (F p y) = 0 → ∃ i, y i = 0 := fun p y hy h => by
    have := (B p).K_lower y hy
    rw [h, abs_zero] at this
    obtain ⟨i, hi, -⟩ := exists_coord_eq_zero_of_monomial (B p).c_pos this
    exact ⟨i, hi⟩
  constructor
  · -- finite ⟹ `s < λ`: otherwise the piece at the minimizing box diverges
    intro hfin
    by_contra hlt'
    have hge : (lam : ℝ) ≤ s := not_lt.1 hlt'
    apply hfin.ne
    have hKp : K (ρ p₀) = 0 := by
      have h := (B p₀).K_upper (e p₀ p₀) (mem_box_self _ (B p₀).r_pos)
      have hprod : ∏ i, e p₀ p₀ i ^ (B p₀).α i = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hT₀.2.1]; exact zero_pow hT₀.2.2.ne')
      rw [hprod, abs_zero, mul_zero] at h
      have hF : chartMap ρ p₀ (e p₀ p₀) = ρ p₀ := chartMap_extChartAt ρ (mem_extChartAt_source p₀)
      rw [hF] at h
      exact abs_nonpos_iff.1 h
    have hφ₀ : 0 < φ (ρ p₀) :=
      hpos _ (ht_mem p₀ (Finset.mem_product.1 hT₀.1).1) hKp
    set L : ℝ := (B p₀).c * (B p₀).C ^ (-s) * (φ (ρ p₀) / 2) with hL
    have hL0 : 0 < L := by have := (B p₀).C_pos; have := (B p₀).c_pos; positivity
    -- the box integral of the monomial diverges at `i₀`
    have hdiv : ∫⁻ y in bx p₀, ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) = ⊤ := by
      by_contra hne
      have := (lintegral_box_monomial_lt_top_iff (B p₀).r_pos (B p₀).center (a p₀)).1
        (lt_top_iff_ne_top.2 hne) i₀ hT₀.2.1
      have hle : (lam : ℝ) ≤ s := hge
      rw [hlam, ← hval₀] at hle
      have hα : (0 : ℝ) < (B p₀).α i₀ := by exact_mod_cast hT₀.2.2
      simp only [val] at hle
      push_cast at hle
      rw [div_le_iff₀ hα] at hle
      simp only [a] at this
      linarith
    -- lower bound on the box
    have hbound : ∀ᵐ y ∂volume.restrict (D p₀),
        ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) ≤
          ENNReal.ofReal |(fderiv ℝ (F p₀) y).det| * G (F p₀ y) := by
      filter_upwards [ae_restrict_mem (hDopen p₀).measurableSet,
        ae_restrict_of_ae ae_coord_ne_zero] with y hy hy0
      have hKpos : 0 < K (F p₀ y) := lt_of_le_of_ne (hKF p₀ y) (Ne.symm hy.2)
      have hKup : K (F p₀ y) ≤ (B p₀).C * |∏ i, y i ^ (B p₀).α i| := by
        have := (B p₀).K_upper y hy.1; rwa [abs_of_nonneg (hKF p₀ y)] at this
      have hJ := (B p₀).J_lower y hy.1
      have hφy := (B p₀).φ_lower hφ₀ y hy.1
      have hm := abs_monomial_pos hy0 (B p₀).α
      have hmβ := abs_nonneg (∏ i, y i ^ (B p₀).β i)
      have hrp : ((B p₀).C * |∏ i, y i ^ (B p₀).α i|) ^ (-s) ≤ K (F p₀ y) ^ (-s) :=
        rpow_le_rpow_of_nonpos hKpos hKup (by linarith)
      simp only [G]
      rw [ENNReal.ofReal_rpow_of_pos hKpos, ← ENNReal.ofReal_prod_of_nonneg
          fun i _ => rpow_nonneg (abs_nonneg _) _, ← ENNReal.ofReal_mul hL0.le,
        ← ENNReal.ofReal_mul (rpow_nonneg (hKF p₀ y) _), ← ENNReal.ofReal_mul (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← abs_monomial_mul_rpow hy0, hL]
      have h1 : (B p₀).c * |∏ i, y i ^ (B p₀).β i| ≤ |(fderiv ℝ (F p₀) y).det| := hJ
      have h2 : (B p₀).C ^ (-s) * |∏ i, y i ^ (B p₀).α i| ^ (-s) ≤ K (F p₀ y) ^ (-s) := by
        rwa [mul_rpow (B p₀).C_pos.le hm.le] at hrp
      have hCp := (B p₀).C_pos
      have hC0 : 0 ≤ (B p₀).C ^ (-s) * |∏ i, y i ^ (B p₀).α i| ^ (-s) := by positivity
      calc (B p₀).c * (B p₀).C ^ (-s) * (φ (ρ p₀) / 2) *
            (|∏ i, y i ^ (B p₀).β i| * |∏ i, y i ^ (B p₀).α i| ^ (-s))
          = ((B p₀).c * |∏ i, y i ^ (B p₀).β i|) *
              (((B p₀).C ^ (-s) * |∏ i, y i ^ (B p₀).α i| ^ (-s)) * (φ (ρ p₀) / 2)) := by ring
        _ ≤ |(fderiv ℝ (F p₀) y).det| * (K (F p₀ y) ^ (-s) * φ (F p₀ y)) :=
          mul_le_mul h1 (mul_le_mul h2 hφy (by linarith) (rpow_nonneg (hKF p₀ y) _))
            (mul_nonneg hC0 (by linarith)) (abs_nonneg _)
    -- the box minus `D p₀` is null
    have hnull : volume (bx p₀ \ D p₀) = 0 := by
      refine measure_mono_null (fun y hy => ?_) volume_coord_eq_zero
      by_contra hne
      exact hy.2 ⟨hy.1, fun h => hne (hzero_coord p₀ y hy.1 h)⟩
    refine top_le_iff.1 ?_
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal L * ∫⁻ y in bx p₀, ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) := by
          rw [hdiv, ENNReal.mul_top (ENNReal.ofReal_pos.2 hL0).ne']
      _ = ∫⁻ y in bx p₀, ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) :=
          (lintegral_const_mul _ (by fun_prop)).symm
      _ ≤ ∫⁻ y in D p₀ ∪ (bx p₀ \ D p₀), ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) :=
          lintegral_mono_set fun y hy => by
            by_cases h : y ∈ D p₀
            · exact Or.inl h
            · exact Or.inr ⟨hy, h⟩
      _ ≤ ∫⁻ y in D p₀, ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p₀ i) := by
          refine (lintegral_union_le _ _ _).trans ?_
          rw [setLIntegral_measure_zero _ _ hnull, add_zero]
      _ ≤ ∫⁻ y in D p₀, ENNReal.ofReal |(fderiv ℝ (F p₀) y).det| * G (F p₀ y) :=
          lintegral_mono_ae hbound
      _ = ∫⁻ w in F p₀ '' D p₀, G w := (hcov p₀).symm
      _ ≤ ∫⁻ w, G w := setLIntegral_le_lintegral _ _
  · -- `s < λ` ⟹ finite
    intro hlt
    obtain ⟨Φ, hΦ⟩ := hφ.bounded_above_of_compact_support hφc
    have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0)
    have hφle : ∀ w, φ w ≤ Φ := fun w => (le_abs_self _).trans (hΦ w)
    -- the integrand vanishes off the support of `φ`; the zero set of `K` there is null
    let A : Set (EuclideanSpace ℝ (Fin n)) := ⋃ p ∈ t, F p '' D p
    let N : Set (EuclideanSpace ℝ (Fin n)) := tsupport φ ∩ {w | K w = 0}
    have hsupp : Function.support G ⊆ A ∪ N := by
      intro w hw
      have hwφ : w ∈ tsupport φ := by
        by_contra h
        apply hw
        simp [G, image_eq_zero_of_notMem_tsupport h]
      by_cases hKw : K w = 0
      · exact Or.inr ⟨hwφ, hKw⟩
      · obtain ⟨p, hp, y, hy, hFy⟩ := hcover w hwφ
        refine Or.inl (mem_iUnion₂.2 ⟨p, hp, y, ⟨hy, ?_⟩, hFy⟩)
        simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
        rw [hFy]
        exact hKw
    have hN : volume N = 0 := by
      have hsub : N ⊆ ⋃ p ∈ t, F p '' (bx p ∩ {y | ∃ i, y i = 0}) := by
        intro w hw
        obtain ⟨p, hp, y, hy, hFy⟩ := hcover w hw.1
        refine mem_iUnion₂.2 ⟨p, hp, y, ⟨hy, hzero_coord p y hy ?_⟩, hFy⟩
        rw [hFy]
        exact hw.2
      refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
      refine (measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_eq_zero fun p _ => ?_
      refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun y hy => ((B p).diff y hy.1).differentiableWithinAt) ?_
      exact measure_mono_null inter_subset_right volume_coord_eq_zero
    -- each piece is finite
    have hpiece : ∀ p ∈ t, ∫⁻ w in F p '' D p, G w < ⊤ := by
      intro p hp
      set L : ℝ := (B p).C * (B p).c ^ (-s) * Φ with hL
      have hL0 : 0 ≤ L := by have := (B p).C_pos; have := (B p).c_pos; positivity
      have hbound : ∀ᵐ y ∂volume.restrict (D p),
          ENNReal.ofReal |(fderiv ℝ (F p) y).det| * G (F p y) ≤
            ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p i) := by
        filter_upwards [ae_restrict_mem (hDopen p).measurableSet,
          ae_restrict_of_ae ae_coord_ne_zero] with y hy hy0
        have hKpos : 0 < K (F p y) := lt_of_le_of_ne (hKF p y) (Ne.symm hy.2)
        have hKlo : (B p).c * |∏ i, y i ^ (B p).α i| ≤ K (F p y) := by
          have := (B p).K_lower y hy.1; rwa [abs_of_nonneg (hKF p y)] at this
        have hm := abs_monomial_pos hy0 (B p).α
        have hrp : K (F p y) ^ (-s) ≤ ((B p).c * |∏ i, y i ^ (B p).α i|) ^ (-s) :=
          rpow_le_rpow_of_nonpos (by have := (B p).c_pos; positivity) hKlo (by linarith)
        simp only [G]
        rw [ENNReal.ofReal_rpow_of_pos hKpos, ← ENNReal.ofReal_prod_of_nonneg
            fun i _ => rpow_nonneg (abs_nonneg _) _, ← ENNReal.ofReal_mul hL0,
          ← ENNReal.ofReal_mul (rpow_nonneg (hKF p y) _), ← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← abs_monomial_mul_rpow hy0, hL]
        rw [mul_rpow (B p).c_pos.le hm.le] at hrp
        have h1 := (B p).J_upper y hy.1
        have hφy := hφle (F p y)
        have hφ0 : 0 ≤ φ (F p y) ∨ φ (F p y) < 0 := le_or_gt 0 (φ (F p y))
        rcases hφ0 with hφ0 | hφ0
        · have hcC := (B p).C_pos
          have hcc := (B p).c_pos
          calc |(fderiv ℝ (F p) y).det| * (K (F p y) ^ (-s) * φ (F p y))
              ≤ ((B p).C * |∏ i, y i ^ (B p).β i|) *
                  (((B p).c ^ (-s) * |∏ i, y i ^ (B p).α i| ^ (-s)) * Φ) :=
                mul_le_mul h1 (mul_le_mul hrp hφy hφ0 (by positivity))
                  (mul_nonneg (rpow_nonneg (hKF p y) _) hφ0) (by positivity)
            _ = (B p).C * (B p).c ^ (-s) * Φ *
                  (|∏ i, y i ^ (B p).β i| * |∏ i, y i ^ (B p).α i| ^ (-s)) := by ring
        · have : |(fderiv ℝ (F p) y).det| * (K (F p y) ^ (-s) * φ (F p y)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
              (mul_nonpos_of_nonneg_of_nonpos (rpow_nonneg (hKF p y) _) hφ0.le)
          refine this.trans ?_
          have := (B p).c_pos
          positivity
      calc ∫⁻ w in F p '' D p, G w
          = ∫⁻ y in D p, ENNReal.ofReal |(fderiv ℝ (F p) y).det| * G (F p y) := hcov p
        _ ≤ ∫⁻ y in D p, ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p i) :=
            lintegral_mono_ae hbound
        _ ≤ ∫⁻ y in bx p, ENNReal.ofReal L * ∏ i, ENNReal.ofReal (|y i| ^ a p i) :=
            lintegral_mono_set inter_subset_left
        _ = ENNReal.ofReal L * ∫⁻ y in bx p, ∏ i, ENNReal.ofReal (|y i| ^ a p i) :=
            lintegral_const_mul _ (by fun_prop)
        _ < ⊤ := by
            refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              ((lintegral_box_monomial_lt_top_iff (B p).r_pos (B p).center (a p)).2 ?_)
            intro i hci
            simp only [a]
            rcases Nat.eq_zero_or_pos ((B p).α i) with hα | hα
            · simp only [hα, CharP.cast_eq_zero, mul_zero, sub_zero]
              linarith [(Nat.cast_nonneg ((B p).β i) : (0 : ℝ) ≤ (B p).β i)]
            · have hmem : (p, i) ∈ T :=
                Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp, Finset.mem_univ _⟩, hci, hα⟩
              have hle : (lam : ℝ) ≤ (val (p, i) : ℝ) := by exact_mod_cast hlam_le _ hmem
              have hα' : (0 : ℝ) < (B p).α i := by exact_mod_cast hα
              simp only [val] at hle
              push_cast at hle
              have := hlt.trans_le hle
              rw [lt_div_iff₀ hα'] at this
              linarith
    have hAN : ∫⁻ w in A ∪ N, G w ≤ ∫⁻ w in A, G w := by
      refine (lintegral_union_le G A N).trans ?_
      rw [setLIntegral_measure_zero N G hN, add_zero]
    calc ∫⁻ w, G w = ∫⁻ w in A ∪ N, G w := (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ w in A, G w := hAN
      _ ≤ ∑ p ∈ t, ∫⁻ w in F p '' D p, G w := lintegral_finset_biUnion_le _ _ _
      _ < ⊤ := ENNReal.sum_lt_top.2 hpiece

end OpenTheory.Singular
