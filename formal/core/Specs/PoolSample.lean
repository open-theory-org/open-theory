import Specs.PoolRate
import Specs.RateGap
import Checks.PoolSample

/-!
# The kernel-checked sample is the claim types' acceptance

`Checks.poolSample` derives the sampled indices from the beacon blocks and computes each sampled
item's bit itself. This file proves that an accepted check is the acceptance of the claim types
`pool-rate` (`ClaimTypes.poolRate`) and `rate-gap` / `rate-ratio` (`ClaimTypes.rateGap`,
`rateRatio`), given exactly two facts about the request, collected in `Faithful`:

* `block`: position `i` carries the `i`-th block of the seed. The seed is defined as the beacon's
  expansion, so this holds by construction; that the expansion is uniform is assumption A5.
* `item`: the numbers of position `i` are those of the committed item at its index (the
  verifier's Merkle inclusion check; that it binds is assumption A12).

Everything else the guarantee depends on (which items, which bits, how many, the tail bound) is
evaluated by the kernel.
-/

open Finset OpenTheory.Checks OpenTheory.DesignSampling

namespace OpenTheory.PoolSample

variable {N n w : ℕ}

/-- The event a `pool-sample` check counts, on a pool whose item `j` has the numbers `C j`: the
two are equal (`same`: the output is the counted one) or differ (the output fails its label). -/
def Counted (same : Bool) (C : Fin N → ℕ × ℕ) (j : Fin N) : Prop :=
  if same then (C j).1 = (C j).2 else (C j).1 ≠ (C j).2

instance (same : Bool) (C : Fin N → ℕ × ℕ) : DecidablePred (Counted same C) := fun j => by
  unfold Counted; split <;> infer_instance

/-- The request is faithful to the seed and to the committed pool `C`. -/
structure Faithful (C : Fin N → ℕ × ℕ) (seed : Fin n → Fin (2 ^ w)) (xs : List Drawn) : Prop where
  length : xs.length = n
  block : ∀ (i : ℕ) (hi : i < xs.length), xs[i].block = (seed ⟨i, length ▸ hi⟩).val
  item : ∀ (i : ℕ) (hi : i < xs.length) (j : Fin N), xs[i].index = j.val → (xs[i].a, xs[i].c) = C j

theorem drawnLen_eq (xs : List Drawn) : drawnLen xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [drawnLen, ih]

theorem index_of_drawnOk {xs : List Drawn} (h : drawnOk N xs = true) (i : ℕ) (hi : i < xs.length) :
    xs[i].index = xs[i].block % N := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [drawnOk, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => exact h.1
    | succ i => exact ih h.2 i (by simpa using hi)

theorem testBit_drawnBits (same : Bool) (xs : List Drawn) (i : ℕ) (hi : i < xs.length) :
    (drawnBits same xs).testBit i = xs[i].bit same := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [drawnBits]
    cases i with
    | zero =>
      show _ = x.bit same
      rw [Nat.testBit_zero]
      cases x.bit same <;> simp <;> omega
    | succ i =>
      show _ = (xs[i]'(by simpa using hi)).bit same
      rw [Nat.testBit_succ]
      have : (cond (x.bit same) 1 0 + 2 * drawnBits same xs) / 2 = drawnBits same xs := by
        cases x.bit same <;> simp <;> omega
      rw [this]
      exact ih i (by simpa using hi)

theorem bit_eq_decide {same : Bool} {x : Drawn} {C : Fin N → ℕ × ℕ} {j : Fin N}
    (h : (x.a, x.c) = C j) : x.bit same = decide (Counted same C j) := by
  have ha : x.a = (C j).1 := by rw [← h]
  have hc : x.c = (C j).2 := by rw [← h]
  have hb : Nat.beq (C j).1 (C j).2 = decide ((C j).1 = (C j).2) := by
    by_cases e : (C j).1 = (C j).2
    · simp [e]
    · simp only [e, decide_false]
      exact Bool.eq_false_iff.mpr fun hb => e (Nat.eq_of_beq_eq_true hb)
  cases same <;> simp [Drawn.bit, Counted, ha, hc, hb]

/-- **The kernel-checked sample is a `pool-rate` acceptance.** On a faithful request, an accepted
`poolSample` check is `PoolRate.Claim` for the bits of the event on the derived sample. -/
theorem claim_of_poolSample [NeZero N] {C : Fin N → ℕ × ℕ} {seed : Fin n → Fin (2 ^ w)}
    {xs : List Drawn} (hf : Faithful C seed xs) {s l k a b d : ℕ}
    (h : poolSample N s n l k a b d xs = true) :
    PoolRate.Claim (fun i => decide (Counted (Nat.beq s 1) C (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolSample, Bool.and_eq_true] at h
  obtain ⟨⟨hok, -⟩, hc⟩ := h
  convert PoolRate.Claim.of_poolCheck hc using 1
  funext i
  have hi : i.val < xs.length := hf.length ▸ i.isLt
  show _ = (drawnBits (Nat.beq s 1) xs).testBit i
  rw [testBit_drawnBits _ xs i hi]
  refine (bit_eq_decide (hf.item i hi (derive seed i) ?_)).symm
  rw [index_of_drawnOk hok i hi, hf.block i hi]
  rfl

/-- The same with a Chernoff witness. -/
theorem claim_of_poolSampleWitness [NeZero N] {C : Fin N → ℕ × ℕ} {seed : Fin n → Fin (2 ^ w)}
    {xs : List Drawn} (hf : Faithful C seed xs) {s l k a b u v d : ℕ}
    (h : poolSampleWitness N s n l k a b u v d xs = true) :
    PoolRate.Claim (fun i => decide (Counted (Nat.beq s 1) C (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolSampleWitness, Bool.and_eq_true] at h
  obtain ⟨⟨hok, -⟩, hc⟩ := h
  convert PoolRate.Claim.of_poolCheckWitness hc using 1
  funext i
  have hi : i.val < xs.length := hf.length ▸ i.isLt
  show _ = (drawnBits (Nat.beq s 1) xs).testBit i
  rw [testBit_drawnBits _ xs i hi]
  refine (bit_eq_decide (hf.item i hi (derive seed i) ?_)).symm
  rw [index_of_drawnOk hok i hi, hf.block i hi]
  rfl

/-- **The kernel's check is `ClaimTypes.poolRate`'s acceptance** (the procedure `exact-match`:
an item fails when its output differs from its label, `s = 0`). -/
theorem poolRate_accepts [NeZero N] {C : Fin N → ℕ × ℕ} {seed : Fin n → Fin (2 ^ w)}
    {xs : List Drawn} (hf : Faithful C seed xs) {l k a b d : ℕ}
    (h : poolSampleK N 0 n l k a b d xs = true) :
    PoolRate.Claim (fun i => decide (Counted false C (derive seed i))) k ((a : ℝ) / b) (1 / d) := by
  rw [poolSampleK_eq] at h
  exact claim_of_poolSample hf h

/-- **Four kernel checks are a `rate-gap` acceptance.** Pool `A`'s sample, faithful to the seed's
first `nA` blocks, checked for the counted output (`s = 1`) and its complement (`s = 0`); the same
for `B` on the next `nB` blocks. -/
theorem rateGap_accepts {NA NB nA nB : ℕ} [NeZero NA] [NeZero NB]
    {CA : Fin NA → ℕ × ℕ} {CB : Fin NB → ℕ × ℕ} {s : Fin (nA + nB) → Fin (2 ^ w)}
    {xsA xsB : List Drawn} (hA : Faithful CA (RateGap.seedA s) xsA)
    (hB : Faithful CB (RateGap.seedB s) xsB) {lA kA aA bA dA lA' kA' aA' bA' dA' lB kB aB bB dB
      lB' kB' aB' bB' dB' : ℕ}
    (h1 : poolSampleK NA 1 nA lA kA aA bA dA xsA = true)
    (h2 : poolSampleK NA 0 nA lA' kA' aA' bA' dA' xsA = true)
    (h3 : poolSampleK NB 1 nB lB kB aB bB dB xsB = true)
    (h4 : poolSampleK NB 0 nB lB' kB' aB' bB' dB' xsB = true) :
    RateGap.Claim (Counted true CA) (Counted true CB) s
      ⟨kA, kA', kB, kB', (aA : ℝ) / bA, (aA' : ℝ) / bA', (aB : ℝ) / bB, (aB' : ℝ) / bB'⟩
      (1 / dA) (1 / dA') (1 / dB) (1 / dB') := by
  rw [poolSampleK_eq] at h1 h2 h3 h4
  have c1 := claim_of_poolSample hA h1
  have c2 := claim_of_poolSample hA h2
  have c3 := claim_of_poolSample hB h3
  have c4 := claim_of_poolSample hB h4
  have neg : ∀ {M : ℕ} (C : Fin M → ℕ × ℕ) (j : Fin M),
      decide (¬ Counted true C j) = decide (Counted false C j) := by
    intro M C j; simp [Counted]
  refine ⟨c1, ?_, c3, ?_⟩
  · simpa only [neg, show Nat.beq 0 1 = false from rfl] using c2
  · simpa only [neg, show Nat.beq 0 1 = false from rfl] using c4

end OpenTheory.PoolSample
