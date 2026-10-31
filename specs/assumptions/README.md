# Assumptions

A certificate lists the ids it relies on. Nothing else may be assumed.
`tests/regression/check_catalog.py` reads the `## A…` headings below.

## A1-iid: held-out examples are IID draws from the target distribution

Mathematical: `sampleLaw P.law n` in Lean. Not checkable from the data. The certificate is about
the distribution the examples were drawn from, not about a shifted one.

## A2-heldout-independent: the held-out set did not influence the model

The model was fixed before the held-out rows were seen. Protocol: commit the hash of the
held-out set before training, and draw the selection from a public randomness beacon. Not provable in Lean.

## A3-model-binding: the certified function is the deployed model

The certificate is about the exact integer function in the Lean file, for example
`QuantizedMLP.errorCountOfWeights` on the listed codes. That this is what runs in production
requires a hash binding (open weights) or attestation (served models). See `../evidence/`.

## A4-labels: held-out labels are the ground truth

The error count is relative to the labels provided. Wrong labels give a bound on disagreement with them, not on true error.

## A5-beacon: the beacon round is unpredictable, and its expansion is uniform

The drand round used as the seed could not be predicted before it was published. Its SHA-256
expansion into `n` blocks is modelled as uniform on `(Fin 2²⁵⁶)ⁿ` (random-oracle model). Used by
`pool-rate`. drand is a threshold network: this fails only if enough of its members collude.

## A6-timestamp: the ordering evidence is honest

The log checkpoint or RFC 3161 token that shows the commitment existed before the beacon round
was not backdated. Used by `pool-rate`.

## A7-issuer-identity: all attempts are made under one issuer key

Attempt accounting sums `δ` over the commitments the issuer declares for a round. Undeclared
commitments and attempts under other identities are not counted; a transparency log (planned)
makes undeclared commitments detectable. Used by `pool-rate`.

## A8-log-complete: the pool is all of the period's traffic

Needed only to read a `pool-rate` claim as a rate on traffic rather than on the committed pool.
Made auditable by giving users signed receipts with inclusion proofs.

## A9-gold-labels: the audit's gold labels define failure

`judged-rate` bounds the rate of failures against gold labels, supplied after sampling for the
audited items by a labeller independent of the issuer. The bound holds if they are the labels that a
rule fixed before the round would give. Used by `judged-rate`.
