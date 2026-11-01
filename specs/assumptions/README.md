# Assumptions

A certificate lists the ids it relies on. Nothing else may be assumed.
`tests/regression/check_catalog.py` reads the `## A…` headings below.

**Every assumption bridges one Lean object of a claim type to the world** (`Specs/ClaimType.lean`):
the proof is about the objects in Lean, and the assumption says that one of them is the real one.
Its `**Bridges:**` line names which, and `tests/regression/check_specs.py` requires one of:

| Bridges | The Lean object | Assumptions |
| --- | --- | --- |
| `law` | the law of the evidence (`law`, `δ`) | A1, A2, A5, A6, A7 |
| `observable` | what the property tests (labels, events) | A4, A9 |
| `domain` | the population the claim is about | A8, A10, A12 |
| `model` | the model the claim is about (`model`) | A3, A11 |

## A1-iid: held-out examples are IID draws from the target distribution

**Bridges:** law. the evidence law is `sampleLaw D n`, the product of the data distribution.

Mathematical: `sampleLaw P.law n` in Lean. Not checkable from the data. The certificate is about
the distribution the examples were drawn from, not about a shifted one.

## A2-heldout-independent: the held-out set did not influence the model

**Bridges:** law. the model (or the PAC-Bayes prior) is a parameter fixed before the sample, not a function of it.

The model was fixed before the held-out rows were seen. Protocol: commit the hash of the
held-out set before training, and draw the selection from a public randomness beacon. Not provable in Lean.

## A3-model-binding: the certified function is the deployed model

**Bridges:** model. the claim type's `model` is the deployed one.

The certificate is about the exact integer function in the Lean file, for example
`QuantizedMLP.errorCountOfWeights` on the listed codes. That this is what runs in production
requires a hash binding (open weights) or attestation (served models). See `../evidence/`.

## A4-labels: held-out labels are the ground truth

**Bridges:** observable. the labels inside the loss define `Wrong`.

The error count is relative to the labels provided. Wrong labels give a bound on disagreement with them, not on true error.

## A5-beacon: the beacon round is unpredictable, and its expansion is uniform

**Bridges:** law. the evidence law is `seedLaw`, uniform seeds.

The drand round used as the seed could not be predicted before it was published. Its SHA-256
expansion into `n` blocks is modelled as uniform on `(Fin 2²⁵⁶)ⁿ` (random-oracle model). Used by
`pool-rate`. drand is a threshold network: this fails only if enough of its members collude.

## A6-timestamp: the ordering evidence is honest

**Bridges:** law. the seed is drawn after the pool is fixed, so the seed law holds given the pool.

The log checkpoint or RFC 3161 token that shows the commitment existed before the beacon round
was not backdated. Used by `pool-rate`.

## A7-issuer-identity: all attempts are made under one issuer key

**Bridges:** law. the declared attempts are all the draws, so `δ` sums over all of them.

Attempt accounting sums `δ` over the commitments the issuer declares for a round. Undeclared
commitments and attempts under other identities are not counted; a transparency log (planned)
makes undeclared commitments detectable. Used by `pool-rate`.

## A8-log-complete: the pool is all of the period's traffic

**Bridges:** domain. the committed pool is the period's traffic.

Needed only to read a `pool-rate` claim as a rate on traffic rather than on the committed pool.
Made auditable by giving users signed receipts with inclusion proofs.

## A9-gold-labels: the audit's gold labels define failure

**Bridges:** observable. the gold labels define the true event.

`judged-rate` bounds the rate of failures against gold labels, supplied after sampling for the
audited items by a labeller independent of the issuer. The bound holds if they are the labels that a
rule fixed before the round would give. Used by `judged-rate`.

## A10-group-membership: each item's pool is its group

**Bridges:** domain. each pool of the pair is its group.

`rate-gap` and `rate-ratio` compare two committed pools, one per group. The claim is about the
groups as recorded or inferred when the pools were committed: protected attributes are often
missing in credit data and inferred (for example by a proxy model), and the claim is then about the
inferred groups. Used by `rate-gap`, `rate-ratio`.


## A11-tree-translation: the integer ensemble computes the deployed model's decisions

**Bridges:** model. the integer ensemble is the deployed LightGBM model, scaled.

`tree-robust` and `tree-monotone` are about the integer ensemble in the request. The producer
(`methods/trees/tree_certificate.py`) reads the deployed model (a LightGBM dump) and scales each
feature and the leaves by powers of two, exactly, since doubles are dyadic. The two models then take
the same decision on every input without missing values, provided the deployed runtime compares
`x ≤ threshold` in the same precision as its dump. Not covered: missing values (`NaN` routing by
`default_left`), categorical splits and `missing_type: Zero` (both refused), and preprocessing
before the model. Anyone can re-run the deterministic translation from the model file to check
it. Used by `tree-robust`, `tree-monotone`.

## A12-commitment-binding: the checked items are the committed ones

**Bridges:** domain. the items the kernel checks are the committed pool's items at their indices.

The kernel derives each sampled index and computes each sampled item's bit from the bytes the
verifier gives it (`Checks.poolSample`). That those bytes are the committed item at that index is
the verifier's Merkle inclusion check against the committed root: it binds if SHA-256 is collision
resistant, and if the verifier's SHA-256 and Merkle code are correct. This is the `item` field of
`PoolSample.Faithful`, the one hypothesis of `PoolSample.poolRate_accepts` and `rateGap_accepts`
besides the seed being the beacon's expansion (A5). Used by `pool-rate`, `judged-rate`,
`rate-gap`, `rate-ratio`.
