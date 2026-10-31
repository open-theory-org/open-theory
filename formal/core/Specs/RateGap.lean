import Foundations.Probability.SeedBlocks
import Specs.Instances

/-!
# Claim template `rate-gap`, v0.1

A spec on a **pair of domains**: two committed pools `A` and `B` (for example the scored
applications of two groups) and a property of their items fixed before the beacon round (for
example "approved"). One round samples both: the first `nA` blocks of the seed pool `A`, the next
`nB` pool `B` (each pool's blocks are uniform, `DesignSampling.seedFrac_restrict`). On each sample
two `pool-rate` claims bound the pool's rate from above (`p`) and, through the complement, from
below (`1 − q`).

Three aggregates on the pair, each with the guarantee `Sound` over the seed
(`specs/taxonomy.md`):

* `interval_sound`: `rA ∈ [1 − qA, pA]` and `rB ∈ [1 − qB, pB]`;
* `gap_sound`: `|rA − rB| ≤ max (pA + qB − 1) (pB + qA − 1)` (demographic parity difference when the
  property is approval and the pools are groups);
* `ratio_sound`: `c · rB ≤ rA` when the claim also has `c · pB ≤ 1 − qA` (the four-fifths rule is
  `c = 4/5`).

The probability of accepting a false claim is at most
`(1 + NA/2^b)^nA (δA + δA') + (1 + NB/2^b)^nB (δB + δB')` (`bad_frac`), uniformly over the counts
and bounds the certifier chooses after seeing the sample. Choosing the pools chooses the metric:
groups give demographic parity, each group's applicants who repaid give equal opportunity, and the
property "wrong" gives an error-rate gap.
-/

open Finset OpenTheory.BinomialTail OpenTheory.DesignSampling MeasureTheory

namespace OpenTheory.RateGap

variable {NA NB nA nB b : ℕ}

/-- The blocks of pool `A`. -/
def seedA (s : Fin (nA + nB) → Fin (2 ^ b)) : Fin nA → Fin (2 ^ b) :=
  restrictSeed (Fin.castAdd nB) s

/-- The blocks of pool `B`. -/
def seedB (s : Fin (nA + nB) → Fin (2 ^ b)) : Fin nB → Fin (2 ^ b) :=
  restrictSeed (Fin.natAdd nA) s

theorem natAdd_injective : Function.Injective (Fin.natAdd nA : Fin nB → Fin (nA + nB)) :=
  fun i j h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- Seeds on which some `rate-gap` certificate can be wrong. -/
def bad [NeZero NA] [NeZero NB] (eA : Fin NA → Prop) (eB : Fin NB → Prop) (δA δA' δB δB' : ℝ) :
    Set (Fin (nA + nB) → Fin (2 ^ b)) :=
  {s | seedA s ∈ DesignSampling.bad eA δA ∪ DesignSampling.bad (fun j => ¬ eA j) δA'} ∪
    {s | seedB s ∈ DesignSampling.bad eB δB ∪ DesignSampling.bad (fun j => ¬ eB j) δB'}

/-- **Soundness bound.** -/
theorem bad_frac [NeZero NA] [NeZero NB] (eA : Fin NA → Prop) (eB : Fin NB → Prop)
    {δA δA' δB δB' : ℝ} (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB') :
    seedFrac (bad (nA := nA) (nB := nB) (b := b) eA eB δA δA' δB δB') ≤
      (1 + (NA : ℝ) / 2 ^ b) ^ nA * (δA + δA') + (1 + (NB : ℝ) / 2 ^ b) ^ nB * (δB + δB') := by
  unfold bad seedA seedB
  refine (seedFrac_union_le _ _).trans ?_
  rw [seedFrac_restrict (Fin.castAdd_injective nA nB), seedFrac_restrict natAdd_injective]
  have a1 := seedFrac_union_le (n := nA) (b := b) (DesignSampling.bad eA δA)
    (DesignSampling.bad (fun j => ¬ eA j) δA')
  have a2 := seedFrac_union_le (n := nB) (b := b) (DesignSampling.bad eB δB)
    (DesignSampling.bad (fun j => ¬ eB j) δB')
  have r1 := rate_sound (n := nA) (b := b) eA h1
  have r2 := rate_sound (n := nA) (b := b) (fun j => ¬ eA j) h2
  have r3 := rate_sound (n := nB) (b := b) eB h3
  have r4 := rate_sound (n := nB) (b := b) (fun j => ¬ eB j) h4
  rw [mul_add, mul_add]
  linarith

/-- The counts and bounds of a `rate-gap` claim, chosen after seeing the sample. -/
structure Params where
  kA : ℕ
  kA' : ℕ
  kB : ℕ
  kB' : ℕ
  pA : ℝ
  qA : ℝ
  pB : ℝ
  qB : ℝ

/-- The four `pool-rate` claims of a `rate-gap` certificate, on the bits of a seed: pool `A`'s
property and its complement on the blocks of `A`, the same for `B`. -/
structure Claim [NeZero NA] [NeZero NB] (eA : Fin NA → Prop) (eB : Fin NB → Prop)
    [DecidablePred eA] [DecidablePred eB] (s : Fin (nA + nB) → Fin (2 ^ b)) (θ : Params)
    (δA δA' δB δB' : ℝ) : Prop where
  upperA : PoolRate.Claim (fun i => decide (eA (derive (seedA s) i))) θ.kA θ.pA δA
  lowerA : PoolRate.Claim (fun i => decide (¬ eA (derive (seedA s) i))) θ.kA' θ.qA δA'
  upperB : PoolRate.Claim (fun i => decide (eB (derive (seedB s) i))) θ.kB θ.pB δB
  lowerB : PoolRate.Claim (fun i => decide (¬ eB (derive (seedB s) i))) θ.kB' θ.qB δB'

variable [NeZero NA] [NeZero NB] {eA : Fin NA → Prop} {eB : Fin NB → Prop}
  [DecidablePred eA] [DecidablePred eB] {δA δA' δB δB' : ℝ}

/-- Both rates lie in their intervals, or the seed is in `bad`. -/
theorem Claim.sound {s : Fin (nA + nB) → Fin (2 ^ b)} {θ : Params}
    (hc : Claim eA eB s θ δA δA' δB δB') :
    (1 - θ.qA ≤ poolRate eA ∧ poolRate eA ≤ θ.pA ∧ 1 - θ.qB ≤ poolRate eB ∧ poolRate eB ≤ θ.pB) ∨
      s ∈ bad eA eB δA δA' δB δB' := by
  have nA' := poolRate_not eA
  have nB' := poolRate_not eB
  rcases PoolRate.Claim.sound eA (seedA s) hc.upperA with h1 | h1
  · rcases PoolRate.Claim.sound (fun j => ¬ eA j) (seedA s) hc.lowerA with h2 | h2
    · rcases PoolRate.Claim.sound eB (seedB s) hc.upperB with h3 | h3
      · rcases PoolRate.Claim.sound (fun j => ¬ eB j) (seedB s) hc.lowerB with h4 | h4
        · exact Or.inl ⟨by linarith, h1, by linarith, h3⟩
        · exact Or.inr (Or.inr (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h2))
  · exact Or.inr (Or.inl (Or.inl h1))

/-- The failure probability of every `rate-gap` aggregate. -/
noncomputable def δTotal (NA NB nA nB b : ℕ) (δA δA' δB δB' : ℝ) : ℝ :=
  (1 + (NA : ℝ) / 2 ^ b) ^ nA * (δA + δA') + (1 + (NB : ℝ) / 2 ^ b) ^ nB * (δB + δB')

omit [DecidablePred eA] [DecidablePred eB] in
/-- From "some accepted claim has a false target ⇒ the seed is bad" to `Sound`. -/
theorem sound_of_bad {accepts : (Fin (nA + nB) → Fin (2 ^ b)) → Params → Prop}
    {target : Params → Prop} (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB')
    (h : ∀ s θ, accepts s θ → ¬ target θ → s ∈ bad eA eB δA δA' δB δB') :
    Sound (seedLaw (nA + nB) b) accepts target (δTotal NA NB nA nB b δA δA' δB δB') := by
  unfold Sound δTotal
  refine (measure_mono (t := bad eA eB δA δA' δB δB') ?_).trans ?_
  · rintro s ⟨θ, ha, hn⟩
    exact h s θ ha hn
  · rw [seedLaw_apply]
    exact ENNReal.ofReal_le_ofReal (bad_frac eA eB h1 h2 h3 h4)

/-- **Intervals.** Both rates lie in their certified intervals. -/
theorem interval_sound (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB') :
    Sound (seedLaw (nA + nB) b) (fun s θ => Claim eA eB s θ δA δA' δB δB')
      (fun θ => 1 - θ.qA ≤ poolRate eA ∧ poolRate eA ≤ θ.pA ∧
        1 - θ.qB ≤ poolRate eB ∧ poolRate eB ≤ θ.pB)
      (δTotal NA NB nA nB b δA δA' δB δB') :=
  sound_of_bad h1 h2 h3 h4 fun _ _ hc hn => hc.sound.resolve_left hn

/-- **Rate gap** (demographic parity difference for approvals of two groups). -/
theorem gap_sound (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB') :
    Sound (seedLaw (nA + nB) b) (fun s θ => Claim eA eB s θ δA δA' δB δB')
      (fun θ => |poolRate eA - poolRate eB| ≤ max (θ.pA + θ.qB - 1) (θ.pB + θ.qA - 1))
      (δTotal NA NB nA nB b δA δA' δB δB') := by
  refine sound_of_bad h1 h2 h3 h4 fun _ θ hc hn => hc.sound.resolve_left fun hi => hn ?_
  obtain ⟨a1, a2, b1, b2⟩ := hi
  exact abs_sub_le_iff.2 ⟨le_max_of_le_left (by linarith), le_max_of_le_right (by linarith)⟩

/-- **Rate ratio** (the four-fifths rule is `c = 4/5`): a claim with `c · pB ≤ 1 − qA` certifies
`c · rB ≤ rA`. -/
theorem ratio_sound {c : ℝ} (hc0 : 0 ≤ c) (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB)
    (h4 : 0 ≤ δB') :
    Sound (seedLaw (nA + nB) b)
      (fun s θ => Claim eA eB s θ δA δA' δB δB' ∧ c * θ.pB ≤ 1 - θ.qA)
      (fun _ => c * poolRate eB ≤ poolRate eA)
      (δTotal NA NB nA nB b δA δA' δB δB') := by
  refine sound_of_bad h1 h2 h3 h4 fun _ θ ⟨hc, hcq⟩ hn => hc.sound.resolve_left fun hi => hn ?_
  obtain ⟨a1, a2, b1, b2⟩ := hi
  calc c * poolRate eB ≤ c * θ.pB := mul_le_mul_of_nonneg_left b2 hc0
    _ ≤ 1 - θ.qA := hcq
    _ ≤ poolRate eA := a1

end OpenTheory.RateGap
