# Claim: pool rate (`pool-rate`, v0.1)

**Statement.** An issuer commits to a pool of `N` items and to a procedure that gives each item a
bit, for example "the deployed model's logged answer to this item is wrong, as graded by grader G".
A public seed published after both commitments selects `n` items. If at most `k` of the selected
bits are set and `P(Bin(n, p) ≤ k) ≤ δ`, then the fraction of the pool with the bit set is at most
`p`, except on a set of seeds of fraction at most `(1 + N/2^b)ⁿ · δ`.

The claim is about the pool, not about a distribution. Nothing is assumed about how the pool
arose: the randomness comes from the seed.

**Lean.** `OpenTheory.PoolRate.Claim bits k p δ` in `formal/core/Specs/PoolRate.lean`. Its meaning
is `Claim.sound` with `DesignSampling.rate_sound`; publication after selecting among several
committed attempts is `DesignSampling.selective_sound`. Builders: `Claim.of_tail` (exact tail, small
`k`) and `Claim.of_witness` (Chernoff witness, any `n`).

## Protocol

1. **Commit.** `commitment.json` (format `opentheory-pool-commitment/0.1`):
   `{issuer, pool: {root, size}, procedure: {kind}, sample: {n, delta}, beacon: {chain, round}}`.
   `pool.root` is the RFC 9162 Merkle root of the items' canonical JSON. `round` is a future round.
2. **Order.** An RFC 3161 token over the SHA-256 of `commitment.json`, dated before the round is
   published. (Planned: transparency-log checkpoints with witness cosignatures, which also let the
   verifier find undeclared attempts.)
3. **Seed.** Round `r` of the drand mainnet chain (`8990e7a9…`, chained BLS, 30 s), signature `σ`.
   Block `i` is `vᵢ = SHA-256("opentheory/pool-rate/v0.1" ‖ r as u64 BE ‖ σ ‖ i as u64 BE)` read as
   a big-endian integer, so `b = 256`.
4. **Indices.** `idxᵢ = vᵢ mod N`. Sampling is with replacement.
5. **Evidence.** For each `i`: the item at `idxᵢ` and its Merkle inclusion proof; labels for the
   sampled items if the pool does not commit them.
6. **Claim.** `k`, `p = a/b`, `δ = 1/d` (equal to the committed `δ`), and the witness `t = u/v`
   when `Claim.of_witness` is used.

## Procedures (v0.1)

- `exact-match`: each pool item is a JSON object with an `output`. The bit is set when the
  canonical JSON of `output` differs from the canonical JSON of the label. The label is the
  item's `label` if the pool committed it, otherwise the one supplied in `sample.labels` after
  sampling; the report then lists those labels as trusted.

## Bundle

`certificate.json` (claim `count`, `bound`, `delta`, optional Chernoff `witness`), `commitment.json`
(subject), `order.tsr` (RFC 3161 token over the commitment's SHA-256), `beacon.json` (round,
signature, previous signature), `sample.json` (`items` with `index`, `leaf`, `proof`; optional
`labels`), and optional `attempts`: the issuer's other commitments to the same round.

## Verifier checks

1. The RFC 3161 token is over this `commitment.json`, chains to a root in the verifier's trust
   directory (`verifier/attestations/tsa_roots/` or `$OT_TSA_ROOTS`), and is dated before round `r`.
2. The drand signature of round `r` on the chain pinned in `verifier/attestations/drand.py`
   (`py_arkworks_bls12381`, ~3 ms, or `py_ecc`, ~0.4 s).
   Steps 1 and 2 are not optional: without a BLS library or `openssl` the verifier reports that it could
   not run (exit code 2), never a verdict, because an unchecked beacon or ordering lets the issuer
   choose the sample.
3. Every `vᵢ` and `idxᵢ` recomputed; each item's inclusion proof checked against `pool.root`.
4. Every bit recomputed with the committed procedure; the Lean kernel counts them.
5. The registered check `OpenTheory.Checks.poolCheck` (or `poolCheckWitness`; registry names `pool`,
   `pool-witness`) returns `true`
   on the packed bits, evaluated by the Lean kernel (`verified`). `ot verify --compiled` runs it as
   compiled code instead (faster; trusts the Lean compiler, so it is labelled separately and never
   `verified`).
   Its meaning is proved once: `PoolRate.Claim.of_poolCheck` gives the claim, `rate_sound` the bound.
6. **Attempt accounting.** δ is summed over this commitment and every other commitment the issuer
   declares for round `r` (`evidence.attempts`); the report states the total. Undeclared
   commitments are covered only by `A7-issuer-identity` until the log of step 2 exists.

## Assumptions

`A5-beacon`, `A6-timestamp`, `A7-issuer-identity`. To read the rate as a rate on a period's
traffic, add `A8-log-complete`. When the bits come from a harness that the verifier does not
re-run, add `A3-model-binding`. Labels or a grader define what the bit means; that is the scope of
the claim, not an assumption.

## Does not cover

- Items outside the pool: future traffic, other distributions.
- Whether the grader or the labels capture correctness beyond their definition.
- Attempts made under other issuer identities (`A7`).

## Prior art

Fixed audit sets can be gamed by the certified party; committing first and sampling after is the
fix [@luck2026certified]. Committing to test-item hashes and revealing a beacon-selected subset is proposed in
[arXiv:2510.07575](https://arxiv.org/abs/2510.07575). Election risk-limiting audits
[@lindeman2012gentle] use public randomness to bound the risk of a wrong outcome. New here: a
machine-checked proof from seed bits to the bound, accounting for selective publication, and a
certificate the verifier checks end to end.
