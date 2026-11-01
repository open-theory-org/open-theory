# Example: a logistic credit score

`model.json` is a logistic regression in scikit-learn's terms (`intercept_[0]`, `coef_[0]`) over
income (k$), debt ratio, years at the address and late payments. `box_applicant.json` is an
applicant with income between 50 and 56, debt ratio between 0.2 and 0.25, four years at the address
and no late payment.

```bash
lake build ot_kernel
python3 methods/linear/linear_certificate.py robust examples/linear_model/model.json \
  examples/linear_model/box_applicant.json --approve --probability 0.5 --out /tmp/lin-robust
interfaces/cli/ot verify /tmp/lin-robust          # approved on the whole box, σ(score) ≥ 0.5
python3 methods/linear/linear_certificate.py monotone examples/linear_model/model.json 0 --up --out /tmp/lin-mono
interfaces/cli/ot verify /tmp/lin-mono            # the score never decreases in income
```

Each accepted bundle is a claim of [`robust-decision`](../../specs/claims/robust-decision.md) or
[`monotone-feature`](../../specs/claims/monotone-feature.md), with `δ = 0`, under A3 and A11.
