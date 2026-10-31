# judged_rate: an AI judge plus a small gold audit

**Claim.** "At most 11.415% of these 100,000 logged responses are wrong against gold labels",
wrong with probability at most 10⁻⁶, from an AI judge's verdicts on 20,000 sampled responses and
gold labels on 2,000 of them. The same 2,000 gold labels alone give 11.685%. The data are
**synthetic** (`make_pool.py`): the model is wrong on 8% of items, and the judge is fooled by 5% of
the model's errors and raises false alarms on 1% of correct answers.

**How.** The judge's verdict is committed for every pool item before the drand round. The round
picks the sample. On the pool, exactly, `true failures = judged failures + missed − false alarms`
(`DesignSampling.poolRate_rectify`), so the bound is

    true rate ≤ UCB(judged, 20,000 items) + UCB(missed, 2,000) − LCB(false alarms, 2,000)

with each bound an exact binomial tail checked by `FastCheck.poolCheck`, and a union bound over
the three (`JudgedRate.bad_frac`). Gold labels only pay for the judge's mistakes. A bad judge makes
the bound looser, never wrong. With the issuer's own labels as the "judge" this is a label audit.

## Run it

```bash
python3 examples/judged_rate/make_pool.py /tmp/ot-jpool        # pool.jsonl (output + judge) + gold.json

ot certify pool-rate commit --pool /tmp/ot-jpool/pool.jsonl --n 20000 --delta-den 2000000 \
    --audit-m 2000 --audit-delta-den 4000000 --alarms-delta-den 4000000 \
    --issuer my-org --out /tmp/ot-jcommit                    # δ = 1/2e6 + 1/4e6 + 1/4e6 = 1e-6

ot certify pool-rate prove --commitment /tmp/ot-jcommit --pool /tmp/ot-jpool/pool.jsonl \
    --gold /tmp/ot-jpool/gold.json --out /tmp/ot-jbundle      # after the round (~90 s)

OT_TSA_ROOTS=<dir with the test root> ot verify /tmp/ot-jbundle   # kernel check, ~2 s; --compiled ~0.4 s, not verified
```

## When the judge helps

The gold-only bound has width about `√(2 p ln(1/δ) / m)` for a failure rate `p`; the audit parts
only pay `≈ ln(1/δ) / m` for the judge's error rate. The judge helps most when the model's failure
rate is large compared with the judge's error rate, and when the judged sample is much larger than
the gold one. At 10⁻⁶ confidence with 2,000 gold labels the gain here is modest (0.27 points),
because the missed part alone costs about `ln(4·10⁶)/2000 ≈ 0.8%`. Larger gold audits, or
lower confidence, widen the gap; `tests/conformance/judged_rate_verify.py` replays this run.
