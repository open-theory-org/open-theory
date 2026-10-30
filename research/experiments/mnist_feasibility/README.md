# Feasibility: a training-data-only bound for an MNIST network

Numerical study, 2026-10-24. Not a certificate: nothing here is checked in
Lean yet. Script: `research/experiments/mnist_feasibility/mnist_occam_feasibility.py`; raw results:
`research/experiments/mnist_feasibility/results/grid{1,2}.json`.

**Result: 11.6% at 95% confidence from the 60,000 training images alone**,
for a ternary CNN with 2,410 parameters coded in 2,761 bits (train error 4.4%,
test error 3.9%). This equals the best published data-independent MNIST bound
(Lotfi et al. 2022, 11.6% at 0.38 KB) and is non-vacuous by a wide margin, so
a checked certificate is worth building.

## Method

- **Bound.** Binomial Occam: with prefix-free code lengths `L(h)`, with
  probability `≥ 1 - δ` every `h` satisfies `P(Bin(n, R_h) ≤ K_h) > δ 2^{-L(h)}`.
  The certified rate is the Clopper–Pearson bound at level `δ 2^{-L(h)}`. Now
  proved in Lean as `OpenTheory.BinomialTail.occam_binomial`.
- **Code.** Configuration index (`log2 110` bits for the 110 configurations
  evaluated); per layer, the counts of `-1` and `+1` weights, then the
  ternary weights by an enumerative code given the counts; integer biases by
  a signed Elias-δ code.
- **Training errors** are counted by an exact integer forward pass (integer
  pixels in `[0, 255]`, ternary weights, integer biases, ReLU, argmax with the
  first maximum winning), i.e. the semantics a Lean certificate would check.
- **Training.** Straight-through ternary quantization, Adam, 20–40 epochs.

## Results

Best configurations, all charged for 110 configurations:

| Model | Params | Bits | Train err | Test err | Bound (95%) |
| --- | --- | --- | --- | --- | --- |
| CNN 5×5/2 ×4, 3×3/2 ×8, linear | 2,410 | 2,761 | 4.44% | 3.94% | **11.6%** |
| CNN 5×5/2 ×6, 3×3/2 ×12, linear | 3,826 | 4,244 | 3.33% | 3.18% | 12.1% |
| CNN ×4, ×8, 3×3/1 ×8, linear | 1,714 | 2,979 | 4.85% | 4.45% | 12.6% |
| CNN ×8, ×16, ×16, linear | 5,146 | 8,420 | 1.27% | 1.68% | 13.2% |
| Best MLP (7×7 pooled, 32 hidden) | 1,930 | 3,526 | 10.4% | 9.8% | 21.1% |

- Test error never exceeds the bound in any of the 110 networks.
- At confidence `1 - 10⁻⁹` the best bound is 11.65%: the confidence level
  costs only about 26 bits.
- The final linear layer dominates the code length (e.g. 2,914 of 3,818 bits
  in an earlier CNN). A separate sparsity threshold for it gave most of the
  improvement from 13.5% to 11.6%.

## Honesty notes

- The second grid of 90 configurations was designed after seeing the first
  20. Charging all 110 covers the selection in the bound, but the design step
  itself is not verifiable. The final certificate must fix its protocol
  before training.
- IID sampling of MNIST from the population of interest is assumed, as for
  every bound here.
- MLCert (Bagnall & Stewart, AAAI 2019) proved a training-data bound in Coq
  (about 23% error on EMNIST at `1 - 10⁻⁹`), with error counts computed by
  unverified code. The claim to aim for is an end-to-end kernel-checked
  certificate at this tightness, not the first mechanized bound.

## What the Lean certificate needs

1. `occam_binomial` — done.
2. A Lean prior for this code with a proof that its weights sum to at most one
   (two-part codes compose by `tsum_sigma_mul_le_one`; uniform payloads by
   `tsum_uniformWeight`). Elias-δ for biases may be replaced by a code with an
   easier Kraft proof, at a small cost in bits.
3. A packed CNN decoder proved equal to a reference CNN semantics, as done for
   MLPs in `OpenTheory.QuantizedMLPPacked`. Convolution is itself a
   polynomial product, so Kronecker substitution applies directly.
4. Error counts on all 60,000 training images by `decide +kernel`, split into
   files for parallel checking.
