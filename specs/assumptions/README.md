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
