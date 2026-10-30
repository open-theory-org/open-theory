import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theory.Training.Singular.PlateauFlow

/-!
# The matrix Riccati equation `Ṗ = S P + P S - P²` in closed form

For a symmetric `S = Σₐ λₐ wₐ wₐᵀ` (orthonormal basis `w`) and `Z₀ : Hs → V`,

  `P(t) = Y(t) G(t)⁻¹ Y(t)ᵀ`,  `Y(t) = e^{tS} Z₀`,  `G(t) = 1 + Σₐ φ(λₐ, t) gₐ gₐᵀ`,

with `gₐ = Z₀ᵀ wₐ` and `φ(λ, t) = ∫₀ᵗ e^{2λs} ds`, solves the Riccati equation with
`P(0) = Z₀ Z₀ᵀ` (`hasDerivAt_Pc`). It is the unique solution (`eq_Pc`), and its entries in the
eigenbasis are `⟪wₐ, P wᵦ⟫ = e^{(λₐ+λᵦ) t} ⟪gₐ, G⁻¹ gᵦ⟫`. Balanced gradient flow of a two-layer
linear network produces exactly this equation (`OpenTheory.Plateau.BalancedInit`).
-/

noncomputable section
open Real Filter Topology
open scoped RealInnerProductSpace

namespace OpenTheory.Riccati

open OpenTheory.Plateau (unique_of_contDiff)

variable {V Hs : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]

/-- The rank-one map `z ↦ ⟪a, z⟫ a`. -/
def proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : E) : E →L[ℝ] E :=
  (innerSL ℝ a).smulRight a

@[simp] theorem proj_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a z : E) :
    proj a z = ⟪a, z⟫ • a := by
  simp [proj]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : OrthonormalBasis ι ℝ V) (lam : ι → ℝ)

theorem proj_comp_proj (a b : ι) :
    proj (w a) ∘L proj (w b) = if a = b then proj (w a) else 0 := by
  ext z
  split_ifs with h
  · subst h; simp [w.orthonormal.1 a]
  · simp [w.inner_eq_ite, h]

omit [DecidableEq ι] in
theorem sum_proj : ∑ a, proj (w a) = ContinuousLinearMap.id ℝ V := by
  ext z; simp [w.sum_repr']

/-- `S = Σ λₐ wₐ wₐᵀ`. -/
def Sop : V →L[ℝ] V := ∑ a, lam a • proj (w a)

/-- `e^{tS} = Σ e^{λₐ t} wₐ wₐᵀ`. -/
def expS (t : ℝ) : V →L[ℝ] V := ∑ a, exp (lam a * t) • proj (w a)

omit [DecidableEq ι] in
theorem expS_zero : expS w lam 0 = ContinuousLinearMap.id ℝ V := by
  simp [expS, sum_proj]

theorem comp_sum_proj (c d : ι → ℝ) :
    (∑ a, c a • proj (w a)) ∘L (∑ b, d b • proj (w b)) = ∑ a, (c a * d a) • proj (w a) := by
  ext z
  simp [w.inner_eq_ite, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1; ring

theorem hasDerivAt_expS (t : ℝ) : HasDerivAt (expS w lam) (Sop w lam ∘L expS w lam t) t := by
  have h : HasDerivAt (expS w lam) (∑ a, (lam a * exp (lam a * t)) • proj (w a)) t := by
    unfold expS
    refine HasDerivAt.fun_sum fun a _ => ?_
    have := ((hasDerivAt_id t).const_mul (lam a)).exp
    simpa [mul_comm] using this.smul_const (proj (w a))
  rwa [Sop, expS, comp_sum_proj]

theorem expS_add (s t : ℝ) : expS w lam s ∘L expS w lam t = expS w lam (s + t) := by
  rw [expS, expS, comp_sum_proj, expS]
  simp [← Real.exp_add, mul_add]

theorem Sop_comp_expS (t : ℝ) : Sop w lam ∘L expS w lam t = expS w lam t ∘L Sop w lam := by
  rw [Sop, expS, comp_sum_proj, comp_sum_proj]; simp [mul_comm]

/-! ### The closed form -/

/-- `φ(λ, t) = ∫₀ᵗ e^{2λs} ds`. -/
def phi (l t : ℝ) : ℝ := if l = 0 then t else (exp (2 * l * t) - 1) / (2 * l)

theorem hasDerivAt_phi (l t : ℝ) : HasDerivAt (phi l) (exp (2 * l * t)) t := by
  by_cases hl : l = 0
  · subst hl
    have : phi 0 = id := funext fun t => by simp [phi]
    rw [this]; simpa using hasDerivAt_id t
  · have e : phi l = fun t => (exp (2 * l * t) - 1) / (2 * l) := funext fun t => by simp [phi, hl]
    have h := (((hasDerivAt_id' t).const_mul (2 * l)).exp.sub_const 1).div_const (2 * l)
    rw [e]
    convert h using 1
    field_simp

theorem phi_zero (l : ℝ) : phi l 0 = 0 := by unfold phi; split_ifs <;> simp

theorem phi_nonneg (l : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ phi l t := by
  unfold phi
  split_ifs with hl
  · exact ht
  · rcases lt_or_gt_of_ne hl with h | h
    · apply div_nonneg_of_nonpos
      · have : exp (2 * l * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
        linarith
      · linarith
    · apply div_nonneg
      · have : 1 ≤ exp (2 * l * t) := one_le_exp_iff.2 (by positivity)
        linarith
      · linarith

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] (Z₀ : Hs →L[ℝ] V)

/-- `gₐ = Z₀ᵀ wₐ`. -/
def gvec (a : ι) : Hs := ContinuousLinearMap.adjoint Z₀ (w a)

/-- `G(t) = 1 + Σ φ(λₐ, t) gₐ gₐᵀ`. -/
def Gop (t : ℝ) : Hs →L[ℝ] Hs :=
  ContinuousLinearMap.id ℝ Hs + ∑ a, phi (lam a) t • proj (gvec w Z₀ a)

/-- `Y(t) = e^{tS} Z₀`. -/
def Ymap (t : ℝ) : Hs →L[ℝ] V := expS w lam t ∘L Z₀

/-- `Y(t)ᵀ = Z₀ᵀ e^{tS}`. -/
def Ytmap (t : ℝ) : V →L[ℝ] Hs := ContinuousLinearMap.adjoint Z₀ ∘L expS w lam t

omit [DecidableEq ι] in
theorem adjoint_comp_proj_comp (a : ι) :
    ContinuousLinearMap.adjoint Z₀ ∘L proj (w a) ∘L Z₀ = proj (gvec w Z₀ a) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, proj_apply, map_smul, gvec]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem Ytmap_comp_Ymap (t : ℝ) :
    Ytmap w lam Z₀ t ∘L Ymap w lam Z₀ t = ∑ a, exp (2 * lam a * t) • proj (gvec w Z₀ a) := by
  have hE : expS w lam t ∘L expS w lam t = ∑ a, exp (2 * lam a * t) • proj (w a) := by
    rw [expS, comp_sum_proj]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Real.exp_add]; ring_nf
  have : Ytmap w lam Z₀ t ∘L Ymap w lam Z₀ t =
      ContinuousLinearMap.adjoint Z₀ ∘L (expS w lam t ∘L expS w lam t) ∘L Z₀ := by
    simp [Ytmap, Ymap, ContinuousLinearMap.comp_assoc]
  rw [this, hE]
  ext z
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← adjoint_comp_proj_comp w Z₀ a]; rfl

theorem hasDerivAt_Gop (t : ℝ) :
    HasDerivAt (Gop w lam Z₀) (Ytmap w lam Z₀ t ∘L Ymap w lam Z₀ t) t := by
  rw [Ytmap_comp_Ymap]
  unfold Gop
  refine HasDerivAt.const_add _ (HasDerivAt.fun_sum fun a _ => ?_)
  simpa using (hasDerivAt_phi (lam a) t).smul_const (proj (gvec w Z₀ a))

omit [DecidableEq ι] in
theorem inner_Gop_ge {t : ℝ} (ht : 0 ≤ t) (x : Hs) : ‖x‖ ^ 2 ≤ ⟪Gop w lam Z₀ t x, x⟫ := by
  have : ⟪Gop w lam Z₀ t x, x⟫ = ‖x‖ ^ 2 + ∑ a, phi (lam a) t * ⟪gvec w Z₀ a, x⟫ ^ 2 := by
    simp only [Gop, add_apply, ContinuousLinearMap.id_apply, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, proj_apply, inner_add_left, sum_inner,
      real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_comm x]; ring
  rw [this]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
    mul_nonneg (phi_nonneg _ ht) (sq_nonneg _))

omit [DecidableEq ι] in
theorem isUnit_Gop {t : ℝ} (ht : 0 ≤ t) : IsUnit (Gop w lam Z₀ t) := by
  have hinj : Function.Injective (Gop w lam Z₀ t : Hs →ₗ[ℝ] Hs) := by
    intro x y hxy
    have h := inner_Gop_ge w lam Z₀ ht (x - y)
    rw [map_sub] at h
    have hxy' : Gop w lam Z₀ t x - Gop w lam Z₀ t y = 0 := sub_eq_zero.2 hxy
    rw [hxy', inner_zero_left] at h
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  let e := LinearEquiv.ofInjectiveEndo (Gop w lam Z₀ t : Hs →ₗ[ℝ] Hs) hinj
  refine ⟨ContinuousLinearEquiv.toUnit (LinearEquiv.toContinuousLinearEquiv e), ?_⟩
  ext x; rfl

/-- The closed form `P(t) = Y(t) G(t)⁻¹ Y(t)ᵀ`. -/
def Pc (t : ℝ) : V →L[ℝ] V :=
  Ymap w lam Z₀ t ∘L (Ring.inverse (Gop w lam Z₀ t) ∘L Ytmap w lam Z₀ t)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem hasDerivAt_Ymap (t : ℝ) :
    HasDerivAt (Ymap w lam Z₀) (Sop w lam ∘L Ymap w lam Z₀ t) t := by
  have := (hasDerivAt_expS w lam t).clm_comp (hasDerivAt_const t Z₀)
  show HasDerivAt (fun y => expS w lam y ∘L Z₀) _ t
  simpa [Ymap, ContinuousLinearMap.comp_assoc] using this

theorem hasDerivAt_Ytmap (t : ℝ) :
    HasDerivAt (Ytmap w lam Z₀) (Ytmap w lam Z₀ t ∘L Sop w lam) t := by
  have := (hasDerivAt_const t (ContinuousLinearMap.adjoint Z₀)).clm_comp (hasDerivAt_expS w lam t)
  show HasDerivAt (fun y => ContinuousLinearMap.adjoint Z₀ ∘L expS w lam y)
    ((ContinuousLinearMap.adjoint Z₀ ∘L expS w lam t) ∘L Sop w lam) t
  simpa [ContinuousLinearMap.comp_assoc, Sop_comp_expS] using this

theorem hasDerivAt_inv_Gop {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => Ring.inverse (Gop w lam Z₀ s))
      (-(Ring.inverse (Gop w lam Z₀ t) ∘L (Ytmap w lam Z₀ t ∘L Ymap w lam Z₀ t) ∘L
        Ring.inverse (Gop w lam Z₀ t))) t := by
  obtain ⟨u, hu⟩ := isUnit_Gop w lam Z₀ ht
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h1
  have h2 := h1.comp_hasDerivAt t (hasDerivAt_Gop w lam Z₀ t)
  refine h2.congr_deriv ?_
  rw [← hu, Ring.inverse_unit]
  simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

/-- **The closed form solves the Riccati equation.** -/
theorem hasDerivAt_Pc {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (Pc w lam Z₀)
      (Sop w lam ∘L Pc w lam Z₀ t + Pc w lam Z₀ t ∘L Sop w lam - Pc w lam Z₀ t ∘L Pc w lam Z₀ t) t := by
  have h : HasDerivAt (Pc w lam Z₀) _ t := (hasDerivAt_Ymap w lam Z₀ t).clm_comp
    ((hasDerivAt_inv_Gop w lam Z₀ ht).clm_comp (hasDerivAt_Ytmap w lam Z₀ t))
  refine h.congr_deriv ?_
  simp only [Pc, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg]
  abel

omit [DecidableEq ι] in
theorem Pc_zero : Pc w lam Z₀ 0 = Z₀ ∘L ContinuousLinearMap.adjoint Z₀ := by
  have hG : Gop w lam Z₀ 0 = 1 := by
    simp [Gop, phi_zero]; rfl
  simp [Pc, Ymap, Ytmap, expS_zero, hG, Ring.inverse_one]
  rfl

/-- The Riccati vector field `P ↦ S P + P S - P²`. -/
def ricField (S : V →L[ℝ] V) (P : V →L[ℝ] V) : V →L[ℝ] V := S ∘L P + P ∘L S - P ∘L P

omit [FiniteDimensional ℝ V] in
theorem ricField_contDiff (S : V →L[ℝ] V) : ContDiff ℝ 1 (ricField S) := by
  unfold ricField
  have hc : ContDiff ℝ 1 (fun P : V →L[ℝ] V => P) := contDiff_id
  exact ((contDiff_const.clm_comp hc).add (hc.clm_comp contDiff_const)).sub (hc.clm_comp hc)

/-- **Uniqueness.** Any solution of the Riccati equation on `[0, T]` starting at `Z₀ Z₀ᵀ` is the
closed form. -/
theorem eq_Pc {T : ℝ} {P : ℝ → V →L[ℝ] V} (hP : ContinuousOn P (Set.Icc 0 T))
    (hP' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt P (ricField (Sop w lam) (P t)) (Set.Ici t) t)
    (h0 : P 0 = Z₀ ∘L ContinuousLinearMap.adjoint Z₀) :
    Set.EqOn P (Pc w lam Z₀) (Set.Icc 0 T) := by
  refine unique_of_contDiff (ricField_contDiff _) hP hP'
    (fun t ht => (hasDerivAt_Pc w lam Z₀ ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_Pc w lam Z₀ ht.1).hasDerivWithinAt) (h0.trans (Pc_zero w lam Z₀).symm)

/-! ### Quadratic-form facts for `Q = G⁻¹`, `G = 1 + Σ φₐ gₐ gₐᵀ`, `φ ≥ 0` -/

section InverseFacts

variable {G Q : Hs →L[ℝ] Hs} {κ : Type*} [Fintype κ] {g : κ → Hs} {φ : κ → ℝ}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem inner_Gm (hG : G = ContinuousLinearMap.id ℝ Hs + ∑ c, φ c • proj (g c)) (y : Hs) :
    ⟪G y, y⟫ = ‖y‖ ^ 2 + ∑ c, φ c * ⟪g c, y⟫ ^ 2 := by
  subst hG
  simp only [add_apply, ContinuousLinearMap.id_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, proj_apply, inner_add_left, sum_inner,
    real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_comm y]; ring

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem Gm_symm (hG : G = ContinuousLinearMap.id ℝ Hs + ∑ c, φ c • proj (g c)) (x y : Hs) :
    ⟪G x, y⟫ = ⟪x, G y⟫ := by
  subst hG
  simp only [add_apply, ContinuousLinearMap.id_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, proj_apply, inner_add_left,
    inner_add_right, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ⟪x, g a⟫ = ⟪g a, x⟫ from real_inner_comm _ _]; ring

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem Gm_apply (hG : G = ContinuousLinearMap.id ℝ Hs + ∑ c, φ c • proj (g c)) (y : Hs) :
    G y = y + ∑ c, (φ c * ⟪g c, y⟫) • g c := by
  subst hG
  simp [proj_apply, smul_smul]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem G_Q (hu : IsUnit G) (hQ : Q = Ring.inverse G) (x : Hs) : G (Q x) = x := by
  have := Ring.mul_inverse_cancel G hu
  rw [hQ]; exact congrArg (fun T : Hs →L[ℝ] Hs => T x) this

variable (hG : G = ContinuousLinearMap.id ℝ Hs + ∑ c, φ c • proj (g c)) (hφ : ∀ c, 0 ≤ φ c)
  (hu : IsUnit G) (hQ : Q = Ring.inverse G)
include hG hu hQ

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem Q_symm (x z : Hs) : ⟪Q x, z⟫ = ⟪x, Q z⟫ := by
  conv_lhs => rw [← G_Q hu hQ z]
  rw [← Gm_symm hG, G_Q hu hQ]

include hφ

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem norm_Q_sq_le (x : Hs) : ‖Q x‖ ^ 2 ≤ ⟪x, Q x⟫ := by
  have h := inner_Gm hG (Q x)
  rw [G_Q hu hQ] at h
  rw [h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun c _ => mul_nonneg (hφ c) (sq_nonneg _))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem inner_Q_nonneg (x : Hs) : 0 ≤ ⟪x, Q x⟫ :=
  (sq_nonneg _).trans (norm_Q_sq_le hG hφ hu hQ x)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
theorem inner_Q_le (x : Hs) : ⟪x, Q x⟫ ≤ ‖x‖ ^ 2 := by
  have h1 := norm_Q_sq_le hG hφ hu hQ x
  have h2 : ⟪x, Q x⟫ ≤ ‖x‖ * ‖Q x‖ := real_inner_le_norm _ _
  have h3 : ‖Q x‖ ≤ ‖x‖ := by
    by_contra h; push Not at h
    have : ‖x‖ * ‖Q x‖ < ‖Q x‖ ^ 2 := by nlinarith [norm_nonneg x]
    linarith
  calc ⟪x, Q x⟫ ≤ ‖x‖ * ‖Q x‖ := h2
    _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖x‖ ^ 2 := (sq _).symm

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
/-- Cauchy–Schwarz for the form `⟪x, Q z⟫`. -/
theorem inner_Q_sq_le (x z : Hs) : ⟪x, Q z⟫ ^ 2 ≤ ⟪x, Q x⟫ * ⟪z, Q z⟫ := by
  set u := Q x
  set v := Q z
  have hβ : ∀ r : ℝ, 0 ≤ ⟪z, Q z⟫ * (r * r) + 2 * ⟪x, Q z⟫ * r + ⟪x, Q x⟫ := by
    intro r
    have h := inner_Gm hG (u + r • v)
    have hpos : 0 ≤ ⟪G (u + r • v), u + r • v⟫ := by
      rw [h]; exact add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun c _ => mul_nonneg (hφ c) (sq_nonneg _))
    have hGu : G u = x := G_Q hu hQ x
    have hGv : G v = z := G_Q hu hQ z
    rw [map_add, map_smul, hGu, hGv] at hpos
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at hpos
    have e1 : ⟪x, u⟫ = ⟪x, Q x⟫ := rfl
    have e2 : ⟪z, v⟫ = ⟪z, Q z⟫ := rfl
    have e3 : ⟪x, v⟫ = ⟪x, Q z⟫ := rfl
    have e4 : ⟪z, u⟫ = ⟪x, Q z⟫ := by
      show ⟪z, Q x⟫ = ⟪x, Q z⟫
      rw [← Q_symm hG hu hQ, real_inner_comm]
    rw [e1, e2, e3, e4] at hpos
    nlinarith
  have := discrim_le_zero hβ
  unfold discrim at this
  nlinarith

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] in
/-- The signal bound `⟪c g_b, Q (c g_b)⟫ ≤ c² / φ_b`. -/
theorem inner_Q_signal_le (b : κ) (hb : 0 < φ b) (c : ℝ) :
    ⟪c • g b, Q (c • g b)⟫ ≤ c ^ 2 / φ b := by
  set y := Q (c • g b)
  have h := inner_Gm hG y
  rw [G_Q hu hQ] at h
  have hdrop : φ b * ⟪g b, y⟫ ^ 2 ≤ ∑ c', φ c' * ⟪g c', y⟫ ^ 2 :=
    Finset.single_le_sum (f := fun c' => φ c' * ⟪g c', y⟫ ^ 2)
      (fun c' _ => mul_nonneg (hφ c') (sq_nonneg _)) (Finset.mem_univ b)
  have hΨ : ⟪c • g b, y⟫ = c * ⟪g b, y⟫ := real_inner_smul_left _ _ _
  have hge : φ b * ⟪g b, y⟫ ^ 2 ≤ c * ⟪g b, y⟫ := by
    rw [← hΨ, h]; nlinarith [sq_nonneg ‖y‖]
  rw [hΨ, le_div_iff₀ hb]
  have h0 : 0 ≤ c * ⟪g b, y⟫ := by
    rw [← hΨ]; exact inner_Q_nonneg hG hφ hu hQ _
  have key : φ b * (c * ⟪g b, y⟫) ^ 2 ≤ c ^ 2 * (c * ⟪g b, y⟫) := by
    have := mul_le_mul_of_nonneg_left hge (sq_nonneg c)
    nlinarith
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0]; simp [sq_nonneg]
  · have : (c * ⟪g b, y⟫) * φ b * (c * ⟪g b, y⟫) ≤ c ^ 2 * (c * ⟪g b, y⟫) := by nlinarith
    exact le_of_mul_le_mul_right this h0

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs] hφ in
/-- The dual identity `⟪h, d⟫ = ⟪Q h, d⟫ + Σ φ_c ⟪g_c, Q h⟫ ⟪g_c, d⟫`. -/
theorem dual_identity (h d : Hs) :
    ⟪h, d⟫ = ⟪Q h, d⟫ + ∑ c, φ c * ⟪g c, Q h⟫ * ⟪g c, d⟫ := by
  conv_lhs => rw [← G_Q hu hQ h]
  rw [Gm_apply hG, inner_add_left, sum_inner]
  simp only [real_inner_smul_left]

end InverseFacts

end OpenTheory.Riccati
