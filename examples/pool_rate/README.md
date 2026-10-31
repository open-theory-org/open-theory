# pool_rate: certify a failure rate on logged traffic by labelling a sample

**Claim.** "At most 2.926% of these 100,000 logged responses are wrong", wrong with probability
at most 10⁻⁶, from labelling 3,000 of them. Nothing is assumed about how the traffic arose: the
sample is chosen by a public drand round published after the log was committed, so the issuer
cannot pick easy items, and the bound is a theorem about the committed log itself
(`OpenTheory.DesignSampling.rate_sound`). The data here are **synthetic** (`make_pool.py`).

## Run it

```bash
python3 examples/pool_rate/make_pool.py /tmp/ot-pool          # pool.jsonl (100k items) + labels.json

# 1. Before the round: commit to the log, n, δ and a future drand round; timestamp the commitment.
ot certify pool-rate commit --pool /tmp/ot-pool/pool.jsonl --n 3000 --delta-den 1000000 \
    --issuer my-org --out /tmp/ot-commit                     # uses a local TEST timestamp authority

# 2. After the round (~90 s): derive the sample, label it, write the bundle.
ot certify pool-rate prove --commitment /tmp/ot-commit --pool /tmp/ot-pool/pool.jsonl \
    --labels /tmp/ot-pool/labels.json --out /tmp/ot-bundle

# 3. Anyone: verify (~1 s; `--compiled` ~0.2 s). Needs `lake build ot_check`, `openssl` and
#    `pip install py_arkworks_bls12381` (or the slower pure-Python `py_ecc`).
OT_TSA_ROOTS=.ot-test-tsa-roots ot verify /tmp/ot-bundle              # the Lean kernel runs the check: verified
OT_TSA_ROOTS=.ot-test-tsa-roots ot verify /tmp/ot-bundle --compiled   # compiled check, faster, not verified
```

For step 3, put the test authority's `ca.crt` (in `.ot-test-tsa/`) into a directory as `*.pem`
and point `OT_TSA_ROOTS` at it. A real deployment uses `--tsa-url` with a public RFC 3161 authority
(only the commitment's digest is sent), and the verifier's operator chooses which authority roots
to trust in `verifier/attestations/tsa_roots/`.

## What the verifier checks

| Step | Checked by |
| --- | --- |
| Commitment timestamped before the round | RFC 3161 token, against the verifier's trusted roots |
| Round is authentic | BLS signature on the pinned drand mainnet chain |
| Sample is the beacon's | every index recomputed from the round signature; every item's Merkle inclusion in the committed root |
| Failures and bound | each bit recomputed (`output ≠ label`); `FastCheck.poolCheck` counts them and checks the binomial tail (or a Chernoff witness at scale), compiled or in the kernel; its meaning is proved once (`Claim.of_poolCheck`, `rate_sound`) |
| Selective publication | δ summed over every commitment the issuer declares for the round |

The report lists what is assumed (A5 beacon, A6 timestamp authority, A7 one issuer identity) and
what is trusted. Labels supplied after sampling are listed as trusted: the rate is relative to
them. `tests/conformance/pool_rate_verify.py` replays this run from recorded fixtures: 4 honest
variants are accepted and 15 forgeries are rejected, each for the right reason.

## Sample sizes

To certify a failure rate ≤ p with zero observed failures needs about `ln(1/δ)/p` samples:
6,905 for p = 0.1% at δ = 10⁻³, 13,809 at δ = 10⁻⁶. Higher confidence is cheap; a lower rate is not.
