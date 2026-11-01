# Statistical guarantees, formally

A statistical certificate says: **this rate (or error) is at most `p`, except with probability at
most `δ` over how the evidence was drawn.** This page says what is proved about that sentence, what
the kernel computes on each certificate, and what is assumed. It is the statistical part of
[trust.md](trust.md); the objects are defined in [language.md](language.md).

Running example: a bank certifies that **at most 3% of this month's 100,000 credit decisions fail
their review**, from 2,000 decisions sampled by a public beacon.

## 1. Two populations, two sources of randomness

| Population | Randomness `ω` | Assumed about the world | Claim types |
| --- | --- | --- | --- |
| **Committed pool**: the 100,000 decisions, fixed and hashed before sampling | a public beacon round (drand), drawn after the commitment | nothing about the data: the randomness is the sampler's own (design-based inference) | `pool-rate`, `judged-rate`, `rate-gap`, `rate-ratio` |
| **Distribution**: the population the data came from | the draw of an IID sample | that the sample is IID from it (A1), and unseen by the model (A2) | `heldout-error`, `occam-code-error`, `pacbayes-error` |

The committed pool is the stronger claim, and the one for the bank: it needs no assumption on how
the data were generated, only that the beacon is unpredictable and the commitment was made first.

## 2. What is proved, once

Every statistical claim type is a `ClaimType` whose `sound` field is a theorem of the form

```
P {ω | ∃ θ, accepts ω θ ∧ ¬ claim θ} ≤ δ
```

with the following properties, all machine-checked:

| Property | What it rules out | Where |
| --- | --- | --- |
| **Exact finite-sample tails**: the binomial tail itself (Clopper–Pearson [@clopper1934use]), or a Chernoff bound with a checked witness [@chernoff1952measure] | asymptotic or normal approximations; "approximately 95%" | `BinomialTail.clopperPearson`, `ChernoffWitness.binomCdf_le_of_witness` |
| **Uniform over the parameters** `θ` (the count, the bound, the code, the box) | choosing the claim after looking at the data, then quoting a pointwise bound | the `∃ θ` in `Sound` |
| **The beacon's blocks, reduced mod N**: the bias of `block mod N` is paid for, `(1 + N/2²⁵⁶)ⁿ` | treating a modular index as exactly uniform | `DesignSampling.rate_sound` |
| **Selective publication**: `δ` is summed over every commitment the issuer declares for the round | publishing the best of several attempts at the nominal `δ` | `DesignSampling.selective_sound` |
| **Two pools from one round**: each pool gets its own blocks of one seed | reusing the same draws for both groups | `DesignSampling.seedFrac_restrict`, `RateGap.gap_sound` |
| **A judge plus a gold audit**: exact finite-sample prediction-powered bounds [@angelopoulos2023prediction] | an unbiased-but-unbounded correction | `JudgedRate.bad_frac` |
| **Learned models**: Hoeffding over a finite code space (Occam [@blumer1987occam]), Catoni's PAC-Bayes bound [@catoni2007pac] | a bound that ignores that the model was trained on the sample | `occam_sound`, `pacBayes_sound` |
| **Claims combine** by a union bound, with no independence | reporting each line's `δ` as the report's | `Sound.and`, `Sound.comap` |

The arithmetic is exact: the kernel checks integer inequalities (`d · tail ≤ bⁿ`), never a
floating-point value.

## 3. What the kernel computes on each certificate

For a committed pool, the chain from the beacon to the answer is:

```
beacon round (drand)          ── BLS signature checked ─────────── A5: unpredictable
   │ SHA-256 expansion        ── by the verifier ────────────────── A5: uniform (random oracle)
   ▼
seed blocks b₁ … bₙ           ┐
   │ jᵢ = bᵢ mod N            │
   ▼                          │  evaluated by the Lean kernel
sampled indices j₁ … jₙ       │  (Checks.poolSampleK)
   │ bit = [output ≠ label]   │
   ▼                          │
bits, count, tail bound       ┘
   │                          ── PoolSample.poolRate_accepts, then poolRate_sound (proved once)
   ▼
the claim, except with probability δ
```

The items' values `(output, label)` reach the kernel from the verifier, which checks each one's
Merkle inclusion in the committed root (A12). `PoolSample.Faithful` states exactly these two facts
(the blocks are the seed; the values are the committed items), and it is the only hypothesis of
`poolRate_accepts` and `rateGap_accepts`.

| Step | Before | Now |
| --- | --- | --- |
| seed → indices | verifier (Python) | **kernel** |
| indices + items → bits | verifier (Python) | **kernel** |
| bits → count → tail → claim | kernel | kernel |
| item ↔ commitment | verifier (Merkle) | verifier (Merkle), stated as A12 |
| beacon, timestamp, attempts | verifier (BLS, RFC 3161, accounting) | the same, stated as A5, A6, A7 |

For a distribution (`heldout-error`), the kernel re-runs the model on every held-out row and counts
the errors itself (`decide +kernel` on the integer network); the sample's provenance is A1 and A2.

## 4. What is assumed, and why it cannot be proved

| Assumption | Bridges | Why it is outside the proof |
| --- | --- | --- |
| A5 the beacon is unpredictable and its expansion uniform | law | a property of drand's threshold network and of SHA-256 as a random oracle |
| A6 the commitment was timestamped before the round | law | trust in the timestamp authority the verifier chose |
| A7 every attempt is declared | law | a transparency log makes undeclared attempts detectable (planned) |
| A12 the checked items are the committed ones | domain | SHA-256 collision resistance, and the verifier's Merkle code |
| A8 the pool is the traffic; A10 each pool is its group | domain | how the pool was formed |
| A4, A9 the labels | observable | who labels, and when |
| A1, A2 the sample is IID and unseen (distribution claims only) | law | how the data were collected |

None of them is hidden: each certificate lists those it relies on, and `ot verify` rejects one that
omits any.

## 5. Not yet in the kernel

| What | Where it is today | Next |
| --- | --- | --- |
| `judged-rate`'s bits (output, judge label, gold label: three values per item) | the verifier computes the bits; the kernel checks count and tail | a `Drawn` with three values and the bridge to `JudgedRate.Claim` |
| the SHA-256 expansion and Merkle paths | the verifier | stay outside as A5 and A12: computing SHA-256 in the kernel would not remove the cryptographic assumption, and would cost thousands of kernel steps per sampled item |

## 6. Cost

The kernel's time grows with the sample: about 30 ms for 1,000 items, 0.2 s for 5,000 and 1.1 s
for 20,000 (`pool-sample-witness`, measured with `ot_kernel --time`). The compiled lane runs the
same check, proved equal (`runPoolSample_eq`), in 10 ms, 20 ms and 0.1 s (process start
included). Packing the per-item work into
big-integer operations, as for the MLP check, is the plan for sub-millisecond checks.
