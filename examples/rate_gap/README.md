# rate_gap: certified fairness of credit decisions between two groups

**Claim.** "The approval rate of group A is at least 0.8 × that of group B" (the four-fifths rule),
and "the two approval rates differ by at most 9.67%", each wrong with probability at most 10⁻³, from
5,000 sampled decisions per group. The decisions are logged for every application, so the sample
costs no labelling; what sampling buys is that a third party verifies by seeing 10,000 records, not
the whole log. The data are **synthetic** (`make_pools.py`): group A has 30,000 applications
approved at about 55%, group B 40,000 at about 60%.

**How.** Both pools and the counted output (`"approve"`) are committed before a drand round. The
round's first 5,000 blocks sample pool A, the next 5,000 pool B (fixed blocks of a uniform seed are
uniform: `DesignSampling.seedFrac_restrict`). Four exact binomial bounds give an interval for each
rate; `RateGap.gap_sound` and `RateGap.ratio_sound` turn them into the gap and the ratio, with the
single guarantee `Sound` over the round.

## Run it

```bash
python3 examples/rate_gap/make_pools.py /tmp/ot-gpools

ot certify pool-rate commit --pool /tmp/ot-gpools/pool_a.jsonl --n 5000 --delta-den 4000 \
    --pool-b /tmp/ot-gpools/pool_b.jsonl --n-b 5000 --positive '"approve"' \
    --deltas 4000 4000 4000 4000 --issuer my-bank --out /tmp/ot-gcommit     # δ = 4 × 1/4000 = 10⁻³

ot certify pool-rate prove --commitment /tmp/ot-gcommit --pool /tmp/ot-gpools/pool_a.jsonl \
    --pool-b /tmp/ot-gpools/pool_b.jsonl --aggregate ratio --c 4/5 --out /tmp/ot-gbundle

OT_TSA_ROOTS=<dir with the test root> ot verify /tmp/ot-gbundle
```

`--aggregate gap` writes the gap claim instead. Pool A is the group whose rate must not fall below
`c ×` pool B's. The claim is about the groups as committed (`A10-group-membership`): if group
membership is inferred, it is about the inferred groups.

## Sample sizes

The certified gap is the true gap plus both intervals' widths. For rates of 55% and 60%:

| Decisions per group | δ | Certified gap ≤ | Certified ratio ≥ |
| --- | --- | --- | --- |
| 2,000 | 10⁻³ | about 12.7% | about 0.80 |
| 5,000 | 10⁻³ | 9.67% (this run) | 0.846 (this run) |
| 20,000 | 10⁻³ | about 7.4% | about 0.88 |

`tests/conformance/rate_gap_verify.py` replays this run from recorded fixtures: 3 honest variants
accepted, 9 forgeries rejected.
