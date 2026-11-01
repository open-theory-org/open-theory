import Specs.ClaimType
import Specs.Instances
import Specs.RateGap
import Specs.Tree
import Properties.Network
import Specs.Linear
import Specs.MLPExact

/-!
# The claim types

One term of `ClaimType` per claim type of `specs/claims/`: each card names its terms here
(`claim_types = [...]`), and `tests/regression/check_spec_shapes.py` checks that the card's
observable, domain, aggregate and model are those of the term. The specification is stated with
the properties of `Properties/Interface.lean` (one per card, shared by every model family that
provides it) and `Properties/Basic.lean`; the guarantee is the `Sound` theorem proved with the
claim type's check.

| Term | Card | Evidence | δ |
| --- | --- | --- | --- |
| `robustRegion`, `treeRobust` | `robust-decision` | none | `0` |
| `heldOut` | `heldout-error` | IID sample | `δ` |
| `occam` | `occam-code-error` | IID training sample | `2·4ᵈ·exp(−2nε²)` |
| `pacBayes` | `pacbayes-error` | IID sample independent of the prior | `δ` |
| `poolRate` | `pool-rate` | beacon seed | `(1 + N/2^b)ⁿ δ` |
| `judgedRate`, `judgedRateAlarms` | `judged-rate` | beacon seed | sums of the parts |
| `rateGap`, `rateRatio` | `rate-gap`, `rate-ratio` | one beacon round, two pools | `RateGap.δTotal` |
| `treeMonotone` | `monotone-feature` | none | `0` |
| `linearRobust`, `linearMonotone` | `robust-decision`, `monotone-feature` | none | `0` |
| `mlpExact` | `mlp-exact` | none | `0` |
-/

open MeasureTheory

namespace OpenTheory.ClaimTypes

/-- **`robust-decision`**, for ReLU networks: the network decides `c` on every input of a box. -/
noncomputable def robustRegion {m k : ℕ} (g : Exact.Net m k) (r : g.Rules Exact.IntervalRule)
    (θ : g.Params) : ClaimType g.Params (TorchLean.Tensor ℝ [m]) where
  Param := Exact.Box × Fin k
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ bc => OnRegion.certify g r θ bc.1 bc.2 = true
  spec := fun bc => ⟨.property (Decides bc.2), .region {x | Exact.InBox bc.1 x}, .all⟩
  model := fun _ => θ
  δ := 0
  sound := onRegion_sound g r θ

/-- **`heldout-error`**: the error rate on the distribution, from an IID held-out sample. -/
noncomputable def heldOut {H Z : Type*} [MeasurableSpace Z] (ℓ : H → Z → ℝ) (h : H) (n : ℕ)
    (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h)) (δ : ℝ) (D : Measure Z)
    [IsProbabilityMeasure D] : ClaimType H Z where
  Param := ℕ × ℝ
  Evidence := StatLean.StatisticalLearning.Sample Z n
  law := StatLean.StatisticalLearning.sampleLaw D n
  accepts := fun s kp => BinomialTail.numErrors ℓ s h ≤ kp.1 ∧ 0 ≤ kp.2 ∧
    BinomialTail.binomCdf n kp.1 kp.2 ≤ δ
  spec := fun kp => ⟨.property (Wrong ℓ), .distribution inferInstance D, .meanLe kp.2⟩
  model := fun _ => h
  δ := δ
  sound := heldOut_sound h01 hmeas δ D

/-- **`occam-code-error`**: the error rate of a code chosen by training, from the training sample. -/
noncomputable def occam (P : Population QuantizedMLP.Observation) (a : QuantizedMLP.Arch) {n : ℕ}
    (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ClaimType (QuantizedMLP.Code a.parameterCount 4) QuantizedMLP.Observation where
  Param := QuantizedMLP.Code a.parameterCount 4 × ℝ
  Evidence := StatLean.StatisticalLearning.Sample QuantizedMLP.Observation n
  law := StatLean.StatisticalLearning.sampleLaw P.law n
  accepts := fun s cp =>
    StatLean.StatisticalLearning.empRisk (QuantizedMLP.classificationLoss a) s cp.1 + ε ≤ cp.2
  spec := fun cp => ⟨.property (Wrong (QuantizedMLP.classificationLoss a)),
    .distribution inferInstance P.law, .meanLe cp.2⟩
  model := fun cp => cp.1
  δ := 2 * 4 ^ a.parameterCount * Real.exp (-2 * n * ε ^ 2)
  sound := occam_sound P a hn hε

/-- **`pacbayes-error`**: Catoni's bound for a reference code fixed before the sample. -/
noncomputable def pacBayes (P : Population QuantizedMLP.Observation) (a : QuantizedMLP.Arch)
    (c : QuantizedMLP.Code a.parameterCount 4) {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (T : Finset ℝ) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ClaimType (QuantizedMLP.Code a.parameterCount 4) QuantizedMLP.Observation where
  Param := ℝ
  Evidence := StatLean.StatisticalLearning.Sample QuantizedMLP.Observation n
  law := StatLean.StatisticalLearning.sampleLaw P.law n
  accepts := fun s B => ∃ t q γ c' E L : ℝ, t ∈ T ∧ 0 < t ∧ Real.log (1 / (δ / T.card)) ≤ γ ∧
    t * q + (a.parameterCount * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) + γ) / n ≤ c' ∧ 0 ≤ c' ∧
    Real.exp c' ≤ E ∧ L ≤ Real.exp t ∧ 1 < L ∧ (1 - 1 / E) / (1 - 1 / L) ≤ B ∧
    StatLean.StatisticalLearning.empRisk (QuantizedMLP.classificationLoss a) s c ≤ q
  spec := fun B => ⟨.property (Wrong (QuantizedMLP.classificationLoss a)),
    .distribution inferInstance P.law, .meanLe B⟩
  model := fun _ => c
  δ := δ
  sound := pacBayes_sound P a c hm hn T hT hδ

/-- **`pool-rate`**: the rate of an event on a committed pool, from a beacon sample. -/
noncomputable def poolRate {N n b : ℕ} [NeZero N] (e : Fin N → Prop) [DecidablePred e] {δ : ℝ}
    (hδ : 0 ≤ δ) : ClaimType Unit (Fin N) where
  Param := ℕ × ℝ
  Evidence := Fin n → Fin (2 ^ b)
  law := seedLaw n b
  accepts := fun seed kp =>
    PoolRate.Claim (fun i => decide (e (DesignSampling.derive seed i))) kp.1 kp.2 δ
  spec := fun kp => ⟨.property (Event e), .pool N id, .meanLe kp.2⟩
  model := fun _ => ()
  δ := (1 + N / 2 ^ b) ^ n * δ
  sound := poolRate_sound e hδ

/-- **`judged-rate`**: the true failure rate, from a judge on the sample and gold labels on a
prefix. -/
noncomputable def judgedRate {N n m b : ℕ} [NeZero N] (eT eJ : Fin N → Prop) [DecidablePred eT]
    [DecidablePred eJ] (h : m ≤ n) {δJ δA : ℝ} (hJ : 0 ≤ δJ) (hA : 0 ≤ δA) :
    ClaimType Unit (Fin N) where
  Param := ℕ × ℕ × ℝ × ℝ
  Evidence := Fin n → Fin (2 ^ b)
  law := seedLaw n b
  accepts := fun s ps => JudgedRate.Claim (fun i => decide (eJ (DesignSampling.derive s i)))
    (fun i : Fin m => decide (JudgedRate.missed eT eJ (DesignSampling.derive (DesignSampling.prefixSeed h s) i)))
    ps.1 ps.2.1 ps.2.2.1 ps.2.2.2 δJ δA
  spec := fun ps => ⟨.property (Event eT), .pool N id, .meanLe (ps.2.2.1 + ps.2.2.2)⟩
  model := fun _ => ()
  δ := (1 + N / 2 ^ b) ^ n * δJ + (1 + N / 2 ^ b) ^ m * δA
  sound := judgedRate_sound eT eJ h hJ hA

/-- **`judged-rate`** with the false-alarm term: a tighter bound when the judge over-reports. -/
noncomputable def judgedRateAlarms {N n m b : ℕ} [NeZero N] (eT eJ : Fin N → Prop)
    [DecidablePred eT] [DecidablePred eJ] (h : m ≤ n) {δJ δA δB : ℝ} (hJ : 0 ≤ δJ) (hA : 0 ≤ δA)
    (hB : 0 ≤ δB) : ClaimType Unit (Fin N) where
  Param := (ℕ × ℕ × ℕ) × ℝ × ℝ × ℝ
  Evidence := Fin n → Fin (2 ^ b)
  law := seedLaw n b
  accepts := fun s ps =>
    JudgedRate.Claim (fun i => decide (eJ (DesignSampling.derive s i)))
      (fun i : Fin m => decide (JudgedRate.missed eT eJ (DesignSampling.derive (DesignSampling.prefixSeed h s) i)))
      ps.1.1 ps.1.2.1 ps.2.1 ps.2.2.1 δJ δA ∧
    PoolRate.Claim
      (fun i : Fin m => decide (JudgedRate.notAlarm eT eJ (DesignSampling.derive (DesignSampling.prefixSeed h s) i)))
      ps.1.2.2 ps.2.2.2 δB
  spec := fun ps => ⟨.property (Event eT), .pool N id, .meanLe (ps.2.1 + ps.2.2.1 + ps.2.2.2 - 1)⟩
  model := fun _ => ()
  δ := (1 + N / 2 ^ b) ^ n * δJ + (1 + N / 2 ^ b) ^ m * (δA + δB)
  sound := judgedRate_alarms_sound eT eJ h hJ hA hB

/-- **`rate-gap`**: the gap between the rates of an event in two committed pools. -/
noncomputable def rateGap {NA NB nA nB b : ℕ} [NeZero NA] [NeZero NB] (eA : Fin NA → Prop)
    (eB : Fin NB → Prop) [DecidablePred eA] [DecidablePred eB] {δA δA' δB δB' : ℝ}
    (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB') : ClaimType Unit (Fin NA ⊕ Fin NB) where
  Param := RateGap.Params
  Evidence := Fin (nA + nB) → Fin (2 ^ b)
  law := seedLaw (nA + nB) b
  accepts := fun s θ => RateGap.Claim eA eB s θ δA δA' δB δB'
  spec := fun θ => ⟨.property (Event (Sum.elim eA eB)), RateGap.pools NA NB,
    .gapLe (max (θ.pA + θ.qB - 1) (θ.pB + θ.qA - 1))⟩
  model := fun _ => ()
  δ := RateGap.δTotal NA NB nA nB b δA δA' δB δB'
  sound := RateGap.gap_sound h1 h2 h3 h4

/-- **`rate-ratio`**: the ratio of those rates is at least `c` (the four-fifths rule: `c = 4/5`). -/
noncomputable def rateRatio {NA NB nA nB b : ℕ} [NeZero NA] [NeZero NB] (eA : Fin NA → Prop)
    (eB : Fin NB → Prop) [DecidablePred eA] [DecidablePred eB] {δA δA' δB δB' c : ℝ}
    (hc : 0 ≤ c) (h1 : 0 ≤ δA) (h2 : 0 ≤ δA') (h3 : 0 ≤ δB) (h4 : 0 ≤ δB') :
    ClaimType Unit (Fin NA ⊕ Fin NB) where
  Param := RateGap.Params
  Evidence := Fin (nA + nB) → Fin (2 ^ b)
  law := seedLaw (nA + nB) b
  accepts := fun s θ => RateGap.Claim eA eB s θ δA δA' δB δB' ∧ c * θ.pB ≤ 1 - θ.qA
  spec := fun _ => ⟨.property (Event (Sum.elim eA eB)), RateGap.pools NA NB, .ratioGe c⟩
  model := fun _ => ()
  δ := RateGap.δTotal NA NB nA nB b δA δA' δB δB'
  sound := RateGap.ratio_sound hc h1 h2 h3 h4

/-- **`robust-decision`**, for tree ensembles: the decision is `c` on every input of a box. -/
noncomputable def treeRobust (e : Checks.Tree.Ensemble) : ClaimType Checks.Tree.Ensemble (ℕ → ℝ) where
  Param := Checks.Tree.Box × Bool × List Int
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ θ => Checks.Tree.robustCertK e.base e.τ e.trees θ.2.2 θ.1 θ.2.1 = true
  spec := fun θ => ⟨.property (Decides θ.2.1), .region {x | θ.1.Mem x}, .all⟩
  model := fun _ => e
  δ := 0
  sound := treeRobust_sound e

/-- **`monotone-feature`**, for tree ensembles: the score is monotone in one feature on a box. -/
noncomputable def treeMonotone (e : Checks.Tree.Ensemble) :
    ClaimType Checks.Tree.Ensemble ((ℕ → ℝ) × (ℕ → ℝ)) where
  Param := Checks.Tree.Box × ℕ × Bool × List Checks.Tree.Cuts
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ θ => Checks.Tree.monotoneCertK θ.2.1 θ.2.2.1 e.trees θ.1 θ.2.2.2 = true
  spec := fun θ => ⟨.property (MonotoneIn θ.2.1 θ.2.2.1),
    .region {xx | θ.1.Mem xx.1 ∧ θ.1.Mem xx.2}, .all⟩
  model := fun _ => e
  δ := 0
  sound := treeMonotone_sound e

/-- **`robust-decision`**, for linear and logistic-regression models. -/
noncomputable def linearRobust (m : Checks.Linear.LinearModel) : ClaimType Checks.Linear.LinearModel (ℕ → ℝ) where
  Param := Checks.Tree.Box × Bool
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ θ => Checks.Linear.robustK m.bias m.τ m.weights θ.1 θ.2 = true
  spec := fun θ => ⟨.property (Decides θ.2), .region {x | θ.1.Mem x}, .all⟩
  model := fun _ => m
  δ := 0
  sound := linearRobust_sound m

/-- **`monotone-feature`**, for linear and logistic-regression models. -/
noncomputable def linearMonotone (m : Checks.Linear.LinearModel) :
    ClaimType Checks.Linear.LinearModel ((ℕ → ℝ) × (ℕ → ℝ)) where
  Param := Checks.Tree.Box × ℕ × Bool
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ θ => Checks.Linear.monotone m.weights θ.2.1 θ.2.2 = true
  spec := fun θ => ⟨.property (MonotoneIn θ.2.1 θ.2.2), .region {xx | θ.1.Mem xx.1 ∧ θ.1.Mem xx.2}, .all⟩
  model := fun _ => m
  δ := 0
  sound := linearMonotone_sound m

/-- **`mlp-exact`**: a ReLU network `D → hs → o` stored in packed integers outputs exactly the claimed
scores on the claimed input (the packed check of `Checks/MLP.lean`). -/
noncomputable def mlpExact (D : ℕ) (hs : List ℕ) (o : ℕ) :
    ClaimType (Exact.reluMLP D hs o).Params (List ℤ) where
  Param := Checks.MLP.Cert
  Evidence := Unit
  law := Measure.dirac ()
  accepts := fun _ θ => Checks.MLP.check θ.s θ.c θ.wb D θ.a₀ θ.U θ.Y θ.layers = true ∧
    θ.layers.length = hs.length + 1 ∧ Checks.MLP.lastWidth D θ.layers = o
  spec := fun θ => ⟨.property ((Exact.reluMLP D hs o).OutputIs (Checks.MLP.outVec θ.s o θ.Y)),
    .region {Checks.MLP.vec θ.s D θ.U}, .all⟩
  model := fun θ => Checks.MLP.toParams D hs o (Checks.MLP.decode θ.s θ.c D θ.layers)
  δ := 0
  sound := Checks.MLP.mlpExact_sound D hs o

end OpenTheory.ClaimTypes
