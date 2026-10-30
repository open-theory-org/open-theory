import Theory.Learning.PACBayes

/-!
# Product priors and posteriors on parameter codes

A code is a function `Fin p → Fin q`. Priors and posteriors that factor over
coordinates are products of per-coordinate weights. Their total mass,
marginals, and relative entropy then reduce to `p` computations on `Fin q`
instead of `q ^ p` computations on codes.
-/

noncomputable section

namespace OpenTheory.PACBayes

variable {p q : ℕ}

/-- The product of per-coordinate weights. -/
def prodDist (r : Fin p → Fin q → ℝ) : (Fin p → Fin q) → ℝ := fun h => ∏ i, r i (h i)

theorem sum_prodDist (r : Fin p → Fin q → ℝ) : ∑ h, prodDist r h = ∏ i, ∑ v, r i v :=
  (Fintype.prod_sum r).symm

theorem prodDist_isDist {r : Fin p → Fin q → ℝ} (hr : ∀ i, IsDist (r i)) :
    IsDist (prodDist r) :=
  ⟨fun h => Finset.prod_nonneg fun i _ => (hr i).nonneg (h i), by
    rw [sum_prodDist]; simp [(hr _).sum_eq_one]⟩

theorem prodDist_pos {r : Fin p → Fin q → ℝ} (hr : ∀ i v, 0 < r i v) (h : Fin p → Fin q) :
    0 < prodDist r h :=
  Finset.prod_pos fun i _ => hr i (h i)

/-- If the product weight is nonzero, every coordinate weight is nonzero. -/
theorem prodDist_ne_zero {r : Fin p → Fin q → ℝ} {h : Fin p → Fin q}
    (h0 : prodDist r h ≠ 0) (i : Fin p) : r i (h i) ≠ 0 :=
  fun hi => h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)

/-- The `j`-th marginal of a product of probability vectors is its `j`-th factor. -/
theorem sum_prodDist_mul_coord (r : Fin p → Fin q → ℝ) (hr : ∀ i, ∑ v, r i v = 1)
    (j : Fin p) (f : Fin q → ℝ) :
    ∑ h, prodDist r h * f (h j) = ∑ v, r j v * f v := by
  set g : Fin p → Fin q → ℝ := fun i v => r i v * if i = j then f v else 1
  have hg : ∀ h : Fin p → Fin q, prodDist r h * f (h j) = ∏ i, g i (h i) := by
    intro h
    simp only [g, prodDist, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ↓reduceIte]
  simp_rw [hg, ← Fintype.prod_sum]
  rw [Finset.prod_eq_single j]
  · simp [g]
  · intro i _ hij
    simp [g, hij, hr i]
  · simp

/-- Relative entropy is additive over independent coordinates. -/
theorem kl_prodDist {Q π : Fin p → Fin q → ℝ} (hQ : ∀ i, IsDist (Q i))
    (hπ : ∀ i v, 0 < π i v) :
    kl (prodDist Q) (prodDist π) = ∑ i, kl (Q i) (π i) := by
  have key : ∀ h, prodDist Q h * Real.log (prodDist Q h / prodDist π h) =
      ∑ i, prodDist Q h * Real.log (Q i (h i) / π i (h i)) := by
    intro h
    rw [← Finset.mul_sum]
    by_cases h0 : prodDist Q h = 0
    · simp [h0]
    congr 1
    rw [prodDist, prodDist, ← Finset.prod_div_distrib,
      Real.log_prod fun i _ => div_ne_zero (prodDist_ne_zero h0 i) (hπ i (h i)).ne']
  simp only [kl]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_prodDist_mul_coord Q (fun i => (hQ i).sum_eq_one) i
    fun v => Real.log (Q i v / π i v)

/-! ### Uniform posteriors on coordinate sets -/

/-- The uniform probability vector on a nonempty set of levels. -/
def uniformOn (A : Finset (Fin q)) : Fin q → ℝ := fun v => if v ∈ A then 1 / A.card else 0

theorem uniformOn_isDist {A : Finset (Fin q)} (hA : A.Nonempty) : IsDist (uniformOn A) := by
  refine ⟨fun v => by unfold uniformOn; split <;> positivity, ?_⟩
  have hc : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  simp only [uniformOn]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hc]

/-- `KL(Unif(A) ‖ π) = -log |A| + mean_{v ∈ A} (-log π v)`. -/
theorem kl_uniformOn {A : Finset (Fin q)} (hA : A.Nonempty) {π : Fin q → ℝ}
    (hπ : ∀ v, 0 < π v) :
    kl (uniformOn A) π = -Real.log A.card + (∑ v ∈ A, -Real.log (π v)) / A.card := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  simp only [kl, uniformOn]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
  have hout : ∑ v ∈ Finset.univ.filter (· ∉ A),
      (if v ∈ A then 1 / (A.card : ℝ) else 0) *
        Real.log ((if v ∈ A then 1 / (A.card : ℝ) else 0) / π v) = 0 :=
    Finset.sum_eq_zero fun v hv => by simp [(Finset.mem_filter.1 hv).2]
  rw [hout, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hin : ∀ v ∈ A, (if v ∈ A then 1 / (A.card : ℝ) else 0) *
      Real.log ((if v ∈ A then 1 / (A.card : ℝ) else 0) / π v) =
      (-Real.log A.card + -Real.log (π v)) / A.card := by
    intro v hv
    simp only [hv, ↓reduceIte]
    rw [Real.log_div (by positivity) (hπ v).ne', one_div, Real.log_inv]
    field_simp
    ring
  rw [Finset.sum_congr rfl hin, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  field_simp

theorem uniformOn_pos_mem {A : Finset (Fin q)} {v : Fin q} (hv : uniformOn A v ≠ 0) : v ∈ A := by
  by_contra h
  simp [uniformOn, h] at hv

end OpenTheory.PACBayes
