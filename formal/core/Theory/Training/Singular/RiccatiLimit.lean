import Theory.Training.Singular.WindowLimits

/-!
# The Riccati closed form on the plateau window

With `Z₀ = ε Z₁` and eigen-directions `ĝₐ = Z₁ᵀ wₐ`, the entries of the closed form are
`⟪wₐ, P wᵦ⟫ = ⟪hₐ, G⁻¹ hᵦ⟫` with `hₐ = ε e^{λₐ t} ĝₐ` (`inner_w_Pc`). On the window
`t ∈ [c₁, c₂] · log(1/ε)`, if the signal directions `{ĝₐ : a ∈ s}` admit dual vectors
(i.e. are linearly independent), then as `ε → 0`

  `⟪wₐ, P(t) wᵦ⟫ → 2λₐ` if `a = b ∈ s`, and `→ 0` otherwise      (`Pc_entries_limit`).
-/

noncomputable section
open Real Filter Topology Set
open scoped RealInnerProductSpace

namespace OpenTheory.Riccati

variable {V Hs : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : OrthonormalBasis ι ℝ V) (lam : ι → ℝ)

theorem expS_w (t : ℝ) (a : ι) : expS w lam t (w a) = exp (lam a * t) • w a := by
  simp [expS, w.inner_eq_ite]

theorem inner_w_expS (t : ℝ) (a : ι) (v : V) :
    ⟪w a, expS w lam t v⟫ = exp (lam a * t) * ⟪w a, v⟫ := by
  simp [expS, inner_sum, real_inner_smul_right, w.inner_eq_ite]

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ Hs]

omit [DecidableEq ι] in
theorem gvec_smul (Z₁ : Hs →L[ℝ] V) (ε : ℝ) (a : ι) :
    gvec w (ε • Z₁) a = ε • gvec w Z₁ a := by
  simp [gvec]

theorem Ytmap_w (Z₀ : Hs →L[ℝ] V) (t : ℝ) (a : ι) :
    Ytmap w lam Z₀ t (w a) = exp (lam a * t) • gvec w Z₀ a := by
  simp [Ytmap, expS_w, gvec]

/-- Entries of the closed form: `⟪wₐ, P wᵦ⟫ = ⟪e^{λₐt} gₐ, G⁻¹ e^{λᵦt} gᵦ⟫`. -/
theorem inner_w_Pc (Z₀ : Hs →L[ℝ] V) (t : ℝ) (a b : ι) :
    ⟪w a, Pc w lam Z₀ t (w b)⟫ = ⟪exp (lam a * t) • gvec w Z₀ a,
      Ring.inverse (Gop w lam Z₀ t) (exp (lam b * t) • gvec w Z₀ b)⟫ := by
  simp only [Pc, ContinuousLinearMap.comp_apply, Ymap, Ytmap_w]
  rw [inner_w_expS, ← ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left]
  rfl

theorem phi_pos {l t : ℝ} (hl : 0 < l) (ht : 0 < t) : 0 < phi l t := by
  unfold phi
  rw [ite_eq_right hl.ne']
  apply div_pos _ (by linarith)
  have : 1 < exp (2 * l * t) := one_lt_exp_iff.2 (by positivity)
  linarith

/-- **Entries on the plateau window.** -/
theorem Pc_entries_limit (Z₁ : Hs →L[ℝ] V) (s : Finset ι) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₂ : 0 ≤ c₂) (hsig : ∀ a ∈ s, 1 < lam a * c₁) (hnoise : ∀ a ∉ s, lam a * c₂ < 1)
    (d : ι → Hs) (hd : ∀ a ∈ s, ∀ b ∈ s, ⟪gvec w Z₁ a, d b⟫ = if a = b then 1 else 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)), ∀ a b,
      |⟪w a, Pc w lam (ε • Z₁) t (w b)⟫ - (if a = b ∧ a ∈ s then 2 * lam a else 0)| < δ := by
  classical
  set gh := gvec w Z₁
  -- constants
  set K := 1 + ∑ x, ‖gh x‖
  set L := 1 + ∑ x, |4 * lam x|
  set Kd := 1 + ∑ x, ‖d x‖
  set Nι : ℝ := (Fintype.card ι : ℝ)
  have hK1 : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hL1 : 1 ≤ L := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hKd1 : 1 ≤ Kd := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hN0 : 0 ≤ Nι := Nat.cast_nonneg _
  have hghK : ∀ x, ‖gh x‖ ≤ K := fun x => by
    have := Finset.single_le_sum (f := fun x => ‖gh x‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ x)
    simp only [K]; linarith
  have hdK : ∀ x, ‖d x‖ ≤ Kd := fun x => by
    have := Finset.single_le_sum (f := fun x => ‖d x‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ x)
    simp only [Kd]; linarith
  have hlamL : ∀ x, 4 * lam x ≤ L := fun x => by
    have := Finset.single_le_sum (f := fun x => |4 * lam x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
    have := le_abs_self (4 * lam x)
    simp only [L]; linarith
  have hcard : ((Finset.univ.filter (· ∉ s)).card : ℝ) ≤ Nι := by
    simp only [Nι]; exact_mod_cast Finset.card_le_univ _
  clear_value K L Kd Nι
  have hlampos : ∀ a ∈ s, 0 < lam a := fun a ha => by
    have := hsig a ha
    by_contra h; push Not at h; nlinarith
  -- tolerances
  set ηA := min 1 (δ / (K * (K + L) + 1))
  have hηA : 0 < ηA := lt_min one_pos (by positivity)
  set η3 := δ / 2
  set η4 := δ / (2 * (L * Kd * (1 + Nι * K ^ 2)) + 1)
  have hη4 : 0 < η4 := by positivity
  have hη34 : 0 < min η3 η4 := lt_min (by positivity) hη4
  -- eventual facts
  have Eamp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, x ∉ s → ∀ t, 0 ≤ t → t ≤ c₂ * log (1 / ε) →
      ε * exp (lam x * t) < ηA :=
    Filter.eventually_all.2 fun x => by
      by_cases hx : x ∈ s
      · exact Eventually.of_forall fun _ h => absurd hx h
      · filter_upwards [amp_small (hnoise x hx) hηA] with ε hε _ using hε
  have Ewt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, x ∉ s → ∀ t, 0 ≤ t → t ≤ c₂ * log (1 / ε) →
      ε ^ 2 * phi (lam x) t < 1 :=
    Filter.eventually_all.2 fun x => by
      by_cases hx : x ∈ s
      · exact Eventually.of_forall fun _ h => absurd hx h
      · filter_upwards [weight_small (hnoise x hx) hc₂ one_pos] with ε hε _ using hε
  have Esig : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, x ∈ s → ∀ t, c₁ * log (1 / ε) ≤ t →
      |exp (2 * lam x * t) / phi (lam x) t - 2 * lam x| < min η3 η4 ∧
        exp (2 * lam x * t) / phi (lam x) t ≤ 4 * lam x ∧
        exp (lam x * t) / (ε * phi (lam x) t) < min η3 η4 :=
    Filter.eventually_all.2 fun x => by
      by_cases hx : x ∈ s
      · filter_upwards [signal_ratio (hlampos x hx) (hsig x hx) hη34] with ε hε _ using hε
      · exact Eventually.of_forall fun _ h => absurd h hx
  filter_upwards [Eamp, Ewt, Esig, eventually_small] with ε hamp hwt hsg ⟨h0, h1⟩ t ht a b
  have hlog := log_inv_nonneg h0 h1
  have ht0 : 0 ≤ t := le_trans (mul_nonneg hc₁.le hlog) ht.1
  have ht0' : 0 < t := lt_of_lt_of_le (mul_pos hc₁ (Real.log_pos (by
    rw [lt_div_iff₀ h0]; linarith))) ht.1
  -- the inverse and its facts
  set g := gvec w (ε • Z₁)
  have hg : ∀ x, g x = ε • gh x := fun x => gvec_smul w Z₁ ε x
  set φ : ι → ℝ := fun c => phi (lam c) t
  have hφ : ∀ c, 0 ≤ φ c := fun c => phi_nonneg _ ht0
  have hG : Gop w lam (ε • Z₁) t = ContinuousLinearMap.id ℝ Hs + ∑ c, φ c • proj (g c) := rfl
  have hu := isUnit_Gop w lam (ε • Z₁) ht0
  set Q := Ring.inverse (Gop w lam (ε • Z₁) t)
  have hQ : Q = Ring.inverse (Gop w lam (ε • Z₁) t) := rfl
  set h : ι → Hs := fun x => exp (lam x * t) • g x
  have hentry : ∀ x y, ⟪w x, Pc w lam (ε • Z₁) t (w y)⟫ = ⟪h x, Q (h y)⟫ :=
    fun x y => inner_w_Pc w lam _ t x y
  -- diagonal bounds
  have hdiag_noise : ∀ x, x ∉ s → ⟪h x, Q (h x)⟫ ≤ ηA ^ 2 * K ^ 2 := by
    intro x hx
    refine (inner_Q_le hG hφ hu hQ _).trans ?_
    have hnorm : ‖h x‖ = ε * exp (lam x * t) * ‖gh x‖ := by
      simp only [h, hg, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), abs_of_pos h0]
      ring
    rw [hnorm, mul_pow]
    have h1' := hamp x hx t ht0 ht.2
    gcongr
    exact hghK x
  have hdiag_sig : ∀ x, x ∈ s → ⟪h x, Q (h x)⟫ ≤ L := by
    intro x hx
    have hφx : 0 < φ x := phi_pos (hlampos x hx) ht0'
    have := inner_Q_signal_le hG hφ hu hQ x hφx (exp (lam x * t))
    calc ⟪h x, Q (h x)⟫ ≤ exp (lam x * t) ^ 2 / φ x := this
      _ = exp (2 * lam x * t) / φ x := by rw [← exp_nat_mul]; ring_nf
      _ ≤ 4 * lam x := (hsg x hx t ht.1).2.1
      _ ≤ L := hlamL x
  have hdiag_any : ∀ x, ⟪h x, Q (h x)⟫ ≤ ηA ^ 2 * K ^ 2 + L := fun x => by
    by_cases hx : x ∈ s
    · have := hdiag_sig x hx; nlinarith [sq_nonneg (ηA * K)]
    · have := hdiag_noise x hx; linarith
  have hηA1 : ηA ≤ 1 := min_le_left _ _
  have hηAδ : ηA * (K * (K + L)) < δ := by
    have h1 : ηA ≤ δ / (K * (K + L) + 1) := min_le_right _ _
    have h2 : 0 < K * (K + L) + 1 := by positivity
    calc ηA * (K * (K + L)) ≤ δ / (K * (K + L) + 1) * (K * (K + L)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ h2]; nlinarith
  rw [hentry]
  by_cases hab : a ∈ s ∧ b ∈ s
  · -- the signal block: the dual identity
    obtain ⟨ha, hb⟩ := hab
    set y := Q (h b)
    have hyn : ‖y‖ ≤ L := by
      have h1 := norm_Q_sq_le hG hφ hu hQ (h b)
      have h2 := hdiag_sig b hb
      nlinarith [norm_nonneg y]
    have hid := dual_identity hG hu hQ (h b) (d a)
    have hlhs : ⟪h b, d a⟫ = exp (lam b * t) * ε * (if a = b then 1 else 0) := by
      simp only [h, hg, real_inner_smul_left, hd b hb a ha]
      by_cases hab' : a = b
      · subst hab'; simp
      · simp [hab', Ne.symm hab']
    have hsplit : ∑ c, φ c * ⟪g c, y⟫ * ⟪g c, d a⟫ =
        φ a * ⟪g a, y⟫ * ε + ∑ c ∈ Finset.univ.filter (· ∉ s), φ c * ⟪g c, y⟫ * ⟪g c, d a⟫ := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
      congr 1
      rw [Finset.sum_eq_single a]
      · simp [hg, real_inner_smul_left, hd a ha a ha]
      · intro c hc hca
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [hg, real_inner_smul_left]
        rw [hd c hc a ha, ite_eq_right hca]; ring
      · intro h'; simp [ha] at h'
    set R := ∑ c ∈ Finset.univ.filter (· ∉ s), φ c * ⟪g c, y⟫ * ⟪g c, d a⟫
    have hR : |R| ≤ Nι * (K ^ 2 * L * Kd) := by
      have hterm : ∀ c ∈ Finset.univ.filter (· ∉ s),
          |φ c * ⟪g c, y⟫ * ⟪g c, d a⟫| ≤ K ^ 2 * L * Kd := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hw1 := hwt c hc t ht0 ht.2
        have hgy : |⟪g c, y⟫| ≤ ε * ‖gh c‖ * ‖y‖ := by
          rw [hg, real_inner_smul_left, abs_mul, abs_of_pos h0, mul_assoc]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) h0.le
        have hgd : |⟪g c, d a⟫| ≤ ε * ‖gh c‖ * ‖d a‖ := by
          rw [hg, real_inner_smul_left, abs_mul, abs_of_pos h0, mul_assoc]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) h0.le
        rw [abs_mul, abs_mul, abs_of_nonneg (hφ c)]
        calc φ c * |⟪g c, y⟫| * |⟪g c, d a⟫| ≤ φ c * (ε * ‖gh c‖ * ‖y‖) * (ε * ‖gh c‖ * ‖d a‖) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hgy (hφ c)) hgd (abs_nonneg _)
                (mul_nonneg (hφ c) (by positivity))
          _ = (ε ^ 2 * φ c) * ‖gh c‖ ^ 2 * ‖y‖ * ‖d a‖ := by ring
          _ ≤ 1 * K ^ 2 * L * Kd := by
              gcongr
              · exact hghK c
              · exact hdK a
          _ = K ^ 2 * L * Kd := by ring
      calc |R| ≤ ∑ c ∈ Finset.univ.filter (· ∉ s), |φ c * ⟪g c, y⟫ * ⟪g c, d a⟫| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c ∈ Finset.univ.filter (· ∉ s), K ^ 2 * L * Kd := Finset.sum_le_sum hterm
        _ = (Finset.univ.filter (· ∉ s)).card * (K ^ 2 * L * Kd) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Nι * (K ^ 2 * L * Kd) := by
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have hyd : |⟪y, d a⟫| ≤ L * Kd :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hyn (hdK a) (norm_nonneg _) (by linarith))
    have hφa : 0 < φ a := phi_pos (hlampos a ha) ht0'
    have key : ε * φ a * ⟪g a, y⟫ = exp (lam b * t) * ε * (if a = b then 1 else 0) - ⟪y, d a⟫ - R := by
      rw [hsplit] at hid; rw [← hlhs, hid]; ring
    set r := exp (lam a * t) / (ε * φ a)
    have hΨ : ⟪h a, y⟫ = r * (exp (lam b * t) * ε * (if a = b then 1 else 0) - ⟪y, d a⟫ - R) := by
      rw [← key]
      simp only [h, real_inner_smul_left, r]
      field_simp
    obtain ⟨hs1, -, hs3⟩ := hsg a ha t ht.1
    have hr0 : 0 ≤ r := by positivity
    have hr : r < η4 := lt_of_lt_of_le hs3 (min_le_right _ _)
    have herr : r * (|⟪y, d a⟫| + |R|) ≤ δ / 2 * (1 / 1) - 0 ∧ True := by
      constructor
      · have hb2 : |⟪y, d a⟫| + |R| ≤ L * Kd * (1 + Nι * K ^ 2) := by nlinarith
        have hden : 0 < 2 * (L * Kd * (1 + Nι * K ^ 2)) + 1 := by positivity
        calc r * (|⟪y, d a⟫| + |R|) ≤ η4 * (L * Kd * (1 + Nι * K ^ 2)) :=
              mul_le_mul hr.le hb2 (by positivity) hη4.le
          _ ≤ δ / 2 * (1 / 1) - 0 := by
              simp only [η4]
              rw [div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith
      · trivial
    by_cases hab' : a = b
    · subst hab'
      simp only [ha, and_self, ite_true]
      rw [hΨ, ite_eq_left rfl]
      have e : r * (exp (lam a * t) * ε * 1 - ⟪y, d a⟫ - R) - 2 * lam a =
          (exp (2 * lam a * t) / phi (lam a) t - 2 * lam a) - r * (⟪y, d a⟫ + R) := by
        simp only [r, φ]
        rw [show exp (2 * lam a * t) = exp (lam a * t) * exp (lam a * t) by
          rw [← exp_add]; ring_nf]
        field_simp
        ring
      rw [e]
      have h3 : |exp (2 * lam a * t) / phi (lam a) t - 2 * lam a| < δ / 2 :=
        lt_of_lt_of_le hs1 (min_le_left _ _)
      calc |exp (2 * lam a * t) / phi (lam a) t - 2 * lam a - r * (⟪y, d a⟫ + R)|
          ≤ |exp (2 * lam a * t) / phi (lam a) t - 2 * lam a| + |r * (⟪y, d a⟫ + R)| :=
            abs_sub _ _
        _ ≤ |exp (2 * lam a * t) / phi (lam a) t - 2 * lam a| + r * (|⟪y, d a⟫| + |R|) := by
            rw [abs_mul, abs_of_nonneg hr0]
            gcongr; exact abs_add_le _ _
        _ < δ / 2 + δ / 2 := by linarith [herr.1]
        _ = δ := by ring
    · simp only [hab', false_and, ite_false, sub_zero]
      rw [hΨ, ite_eq_right hab', mul_zero, zero_sub, abs_mul, abs_of_nonneg hr0]
      calc r * |-⟪y, d a⟫ - R| ≤ r * (|⟪y, d a⟫| + |R|) := by
            gcongr
            rw [show -⟪y, d a⟫ - R = -(⟪y, d a⟫ + R) by ring, abs_neg]
            exact abs_add_le _ _
        _ ≤ δ / 2 * (1 / 1) - 0 := herr.1
        _ < δ := by linarith
  · -- some index is noise: Cauchy–Schwarz
    have htarget : (if a = b ∧ a ∈ s then 2 * lam a else 0) = 0 := by
      rw [ite_eq_right]
      rintro ⟨rfl, ha⟩; exact hab ⟨ha, ha⟩
    rw [htarget, sub_zero]
    have hcs := inner_Q_sq_le hG hφ hu hQ (h a) (h b)
    have hA0 := inner_Q_nonneg hG hφ hu hQ (h a)
    have hB0 := inner_Q_nonneg hG hφ hu hQ (h b)
    have hprod : ⟪h a, Q (h a)⟫ * ⟪h b, Q (h b)⟫ ≤ ηA ^ 2 * K ^ 2 * (ηA ^ 2 * K ^ 2 + L) := by
      rcases not_and_or.1 hab with ha | hb
      · calc ⟪h a, Q (h a)⟫ * ⟪h b, Q (h b)⟫ ≤ (ηA ^ 2 * K ^ 2) * ⟪h b, Q (h b)⟫ :=
              mul_le_mul_of_nonneg_right (hdiag_noise a ha) hB0
          _ ≤ _ := mul_le_mul_of_nonneg_left (hdiag_any b) (by positivity)
      · calc ⟪h a, Q (h a)⟫ * ⟪h b, Q (h b)⟫ ≤ ⟪h a, Q (h a)⟫ * (ηA ^ 2 * K ^ 2) :=
              mul_le_mul_of_nonneg_left (hdiag_noise b hb) hA0
          _ ≤ (ηA ^ 2 * K ^ 2 + L) * (ηA ^ 2 * K ^ 2) :=
              mul_le_mul_of_nonneg_right (hdiag_any a) (by positivity)
          _ = _ := by ring
    have hsq : ⟪h a, Q (h b)⟫ ^ 2 < δ ^ 2 := by
      have hb1 : ηA ^ 2 * K ^ 2 * (ηA ^ 2 * K ^ 2 + L) ≤ (ηA * (K * (K + L))) ^ 2 := by
        have hη2 : ηA ^ 2 ≤ 1 := pow_le_one₀ hηA.le hηA1
        have hKL : ηA ^ 2 * K ^ 2 + L ≤ (K + L) ^ 2 := by
          have e1 : ηA ^ 2 * K ^ 2 ≤ K ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hη2
          have e2 : L ≤ 2 * K * L + L ^ 2 := by nlinarith
          have e3 : (K + L) ^ 2 = K ^ 2 + 2 * K * L + L ^ 2 := by ring
          linarith
        calc ηA ^ 2 * K ^ 2 * (ηA ^ 2 * K ^ 2 + L) ≤ ηA ^ 2 * K ^ 2 * (K + L) ^ 2 :=
              mul_le_mul_of_nonneg_left hKL (by positivity)
          _ = (ηA * (K * (K + L))) ^ 2 := by ring
      have hb2 : (ηA * (K * (K + L))) ^ 2 < δ ^ 2 :=
        pow_lt_pow_left₀ hηAδ (by positivity) two_ne_zero
      linarith
    exact abs_lt_of_sq_lt_sq hsq hδ.le

end OpenTheory.Riccati
