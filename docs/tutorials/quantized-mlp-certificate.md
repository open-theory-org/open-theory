# Checked generalization certificates for quantized MLPs

Three certificates for trained, deterministic two-bit ReLU networks on the
scikit-learn digits. All come from theorems checked in Lean, with integer
inference and kernel-checked error counts:

| Certificate | Bound sample | Network | Errors | Bound at 95% |
| --- | --- | --- | --- | --- |
| Finite-code Hoeffding (training set) | 1,400 training rows | 16–4–10, 118 params | 325 (23.2%) | **48.2%** |
| PAC-Bayes, learned prior (held-out set) | 397 held-out rows | 64–16–10, 1,210 params | 16 (4.0%) | **7.99%** |
| Exact binomial / Clopper–Pearson (held-out set) | 397 held-out rows | same 64–16–10 network | 16 (4.0%) | **6.06%** |

All bounds are conditional on IID sampling; see **Assumptions** below. The
second and third certify the same network on the same rows; the third is the
tight one, and is what a held-out certificate should report.

## The theorem: Catoni's PAC-Bayes bound

`formal/core/LearningTheory/Generalization/PACBayes.lean` proves, for any probability law `D`,
any measurable loss in `[0,1]` on a finite hypothesis space, any full-support
prior `π` fixed independently of the sample, and any `t`:

with probability at least `1 - δ` over `S ~ Dⁿ`, **every** posterior `Q`
(possibly chosen after seeing `S`) satisfies

```
n Φ_t(R(Q)) ≤ t n R̂_S(Q) + KL(Q ‖ π) + log(1/δ),   Φ_t(p) = -log(1 - (1 - e^{-t}) p).
```

`R(Q)` and `R̂_S(Q)` are the population and empirical risks of the predictor
that draws `h ~ Q` for each prediction (`catoni_pacBayes`). Choosing `t` from
a finite grid `T` costs `log |T|` (`catoni_grid`). Optimising over `t` recovers
the binary-kl bound.

Special cases follow from the choice of prior and posterior:

- **Point-mass posterior on the output of any learner:** the Occam bound with
  code length `log(1/π(h))` (`occam_catoni`). With a uniform prior this is the
  finite-class theorem behind the first certificate.
- **Product prior and posterior on codes:** relative entropy is additive over
  coordinates (`kl_prodDist`), and uniform posteriors on sets of levels have an
  explicit divergence (`kl_uniformOn`). This is the discrete form of
  "flat-minimum" bounds: a posterior that randomizes coordinates the network is
  insensitive to pays less than a point mass.
- **Prior learned on independent data:** the bound sample needs only to be
  independent of the prior. This gives the second certificate.

The proof uses convexity of `exp` (Bernoulli domination), the IID product
measure, Markov's inequality, a finite Donsker–Varadhan inequality (Jensen for
`log`), and convexity of `Φ_t`.

## What the measurements say

Before formalizing the second certificate, the alternatives were measured on
the training rows only. The headline: geometry did not help here.

- **Better concentration with a data-independent prior is marginal.**
  Hoeffding → kl/Catoni moves the first certificate from 47.7% to about 46.8%.
  The 236-bit description length dominates.
- **The trained networks are sharp, not flat.** For the 16–4–10 network, only
  2 of 354 single-coordinate changes keep the training error, and the median
  change adds 98 errors. A quarter of training points have output margin at
  most 4, against a bias unit of 128. Box (uniform-on-levels) posteriors,
  certified exactly by interval propagation, improved data-independent bounds
  by at most 3 points.
- **Noise-injection ("flatness") training made bounds worse.** It cost
  accuracy and did not widen certifiable boxes enough to compensate.
- **With a learned prior, the optimal posterior is the prior centre.** A box
  around the centre costs bits and cannot lower the worst-case error, so with a
  concentrated prior the PAC-Bayes optimum collapses to a held-out bound.
  Stochastic posteriors help only when the prior is diffuse.

Architecture selection used a 700/700 split of the training rows: prior network
on the first half, Dirac-posterior bound with `m = 10` on the second half.

| Inputs | Hidden | Params | Bound on internal split |
| --- | --- | --- | --- |
| pooled 16 | 8 | 226 | 19.8% |
| pooled 16 | 16 | 442 | 19.2% |
| raw 64 | 8 | 610 | 14.1% |
| **raw 64** | **16** | **1,210** | **8.4%** |
| raw 64 | 16, noise 0.3 | 1,210 | 11.4% |
| raw 64 | 24 (900/500 split) | 1,810 | 8.8% |
| raw 64 | 32 | 2,410 | 10.0% |

## Second certificate: protocol

1. **Prior data.** The 1,400 training rows train a 64–16–10 network: raw 8×8
   pixels in `[0,16]`, hidden-bias scale 16, output-bias scale 32. Training is
   straight-through quantized Adam over 6 seeds, then coordinate refinement;
   selection uses training errors only. These rows play no further role.
2. **Prior.** For every code coordinate, the trained level gets mass
   `1 - 3·2⁻²⁰` and each other level `2⁻²⁰` (`centredPrior 20 network`).
   Moving the posterior off the centre costs about 20 bits per coordinate.
3. **Bound data.** The 397 held-out rows, on which the network makes exactly
   16 errors (`heldout_errors`, checked by kernel reduction).
4. **Constants fixed in advance:** `m = 20`, `t ∈ {1/4, …, 2}`, `δ = 1/20`.
5. **Result.** `heldout_pacBayes`: with probability at least 95%, every
   posterior satisfies Catoni's inequality relative to this prior.
   `heldout_certificate` specializes this to the Dirac posterior:
   population error at most `799/10000` (the unrounded Catoni value is
   7.98%). `heldoutSample_fails_iff` ties the event to the realized held-out
   rows.

For comparison, the exact one-sided Clopper–Pearson bound for this one fixed
network is 6.06% (now checked; see the next section), and a single Chernoff-kl
bound gives 6.92%. The gap is what the PAC-Bayes statement costs: it covers
all posteriors and a grid of temperatures simultaneously.

## Third certificate: the exact binomial tail

`formal/core/Verification/Statistical/BinomialTail.lean` proves, for any probability law
`D`, any measurable `{0,1}` loss and one hypothesis fixed independently of the
sample, that the error count `K` of `n` IID draws is exactly binomial:
`P(K ≤ k) = F_{n,R}(k)`, where `R` is the population error and
`F_{n,p}(k) = Σ_{i≤k} C(n,i) pⁱ (1-p)ⁿ⁻ⁱ` (`sampleLaw_count_le`). The proof
decomposes `K ≤ k` into disjoint measurable rectangles, one per set of error
positions. Monotonicity of `F_{n,p}(k)` in `p` comes from the Bernstein
derivative identity `d/dp F_{n,p}(k) = -n b_{n-1,k}(p)`
(`derivative_sum_bernstein`, `binomCdf_antitoneOn`). Two statements follow:

- **Test-set bound** (`testSet_bound`): if `F_{n,p}(k) ≤ δ`, then
  `P(empirical error ≤ k/n ∧ R > p) ≤ δ`. This is the same event as the
  PAC-Bayes certificate, so the two numbers compare directly.
- **Clopper–Pearson, uniform in the observed count** (`clopperPearson`):
  `P(F_{n,R}(K) ≤ δ) ≤ δ`. No error threshold is fixed in advance, and a
  realized sample with at most `k` errors lies in this event whenever `R > p`
  and `F_{n,p}(k) ≤ δ` (`mem_clopperPearson_event`). This closes the gap that
  the threshold 16 was read off the held-out rows.

`examples/certified_accuracy/lean/CertifiedDigits/BinomialMLPDigits.lean` applies both to the saved
network and rows of the second certificate, with `δ = 1/20` and
`p = 303/5000`. `F_{397,p}(16) = N / 5000³⁹⁷` for a natural number `N`, and
`20 N ≤ 5000³⁹⁷` is checked by kernel reduction with linear-time binomial
coefficients (`tailNumerator_le`); the exact value is 0.04976. The unrounded
Clopper–Pearson bound is 6.0571%, so 6.06% loses less than 0.003 points.
The file is hand-written and imports the generated
`PACBayesMLPDigits`; it adds no data.

## Assumptions and disclosures

- **IID.** Both probability statements assume IID observations from the
  population whose risk is bounded. The second also needs the held-out rows to
  be independent of the training rows. A random split of a curated benchmark
  does not establish either. The original
  [UCI dataset](https://archive.ics.uci.edu/dataset/80/optical%2Brecognition%2Bof%2Bhandwritten%2Bdigits)
  contains multiple examples per writer, so writers may be shared across the
  split. The numbers are IID-conditional certificates, not guarantees for new
  writers or deployment data.
- **Held-out hygiene.** No choice in the protocol above used held-out labels.
  However, during exploration the held-out error rates of several preliminary
  models were printed, including the 27.5% of the first certificate's network.
  The candidate architectures for the internal-split selection were drawn up
  after those printouts were seen. This is not verifiable from the artifacts.
- **Fixed decoder.** Decoder, preprocessing and quantization scales are part of
  the hypothesis space and the prior. Changing them after looking at the bound
  data would require charging for the search.

## Checked boundary and reproduction

- `formal/core/Foundations/Models/QuantizedMLP.lean`: the integer decoder. It
  evaluates in linear time by list traversal; `errorCount_codeOfList` lets the
  kernel check saved networks without indexed lookups.
- `formal/core/LearningTheory/Generalization/PACBayes.lean`, `PACBayesCodes.lean`: the general
  theory.
- `formal/core/Verification/Statistical/QuantizedMLP.lean`: the Hoeffding certificate,
  the empirical-risk bridge, and the re-indexing bridge for saved rows.
- `formal/core/Verification/Statistical/QuantizedMLPPACBayes.lean`: the centred prior,
  the generic `dirac_certificate`, and rational inversion of `Φ_t`.
- `formal/core/Verification/Statistical/BinomialTail.lean`: the exact binomial law of the
  error count, the test-set bound and Clopper–Pearson.
- `examples/certified_accuracy/lean/CertifiedDigits/QuantizedMLPDigits.lean`,
  `examples/certified_accuracy/lean/CertifiedDigits/PACBayesMLPDigits.lean`: generated files with the
  saved networks, rows and constants. `BinomialMLPDigits.lean` is hand-written
  on top of the second. They use `decide +kernel`, with no
  `native_decide`, `sorry`, or custom axioms.
- `examples/certified_accuracy/model/digits.json`, `pacbayes_digits64.json`: models,
  rows, provenance (seeds, source-data hashes, library versions) and the
  recomputable certificates.

```bash
python3 methods/statistical/quantized_mlp_certificate.py verify examples/certified_accuracy/model/digits.json
python3 methods/statistical/pacbayes_mlp_certificate.py verify examples/certified_accuracy/model/pacbayes_digits64.json
python3 methods/statistical/pacbayes_mlp_certificate.py export examples/certified_accuracy/model/pacbayes_digits64.json
python3 -m unittest discover -s tests -p "test_*mlp_certificate.py"
lake build
lake env lean tests/QuantizedMLPSmoke.lean
lake env lean tests/PACBayesSmoke.lean
lake env lean tests/BinomialTailSmoke.lean
lake env lean --run verifier/backends/formal/audit_axioms.lean
```

Retraining needs NumPy, PyTorch and scikit-learn; the second artifact records
the versions used (`python3 methods/statistical/pacbayes_mlp_certificate.py train …`).
Verification and export use only the standard library.

The statistical methods are established: Catoni (2007) for the bound,
[Dziugaite & Roy (2017)](https://arxiv.org/abs/1703.11008) and
[Pérez-Ortiz et al. (2021)](https://jmlr.org/papers/v22/20-879.html) for
non-vacuous and learned-prior PAC-Bayes certificates for neural networks. What
is new here is the checked path from a saved network to the number.

For a fixed hypothesis on held-out data, the binomial tail above is the exact
law of the error count, so better concentration has almost nothing left to
give; a tighter held-out number needs more held-out rows or fewer errors. A
sharper bound *from training data alone* would need a model with
a short description that is also accurate, and data with a defensible sampling
model.
