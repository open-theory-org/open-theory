# Example: a credit-style tree ensemble

`model_lightgbm.json` is a three-tree ensemble in the format of LightGBM's `dump_model()`
[@ke2017lightgbm], over income (k$), debt ratio and age; a raw score `≥ 0` approves.
`box_applicant.json` is an applicant with income between 50 and 56, debt ratio between 0.2 and
0.25, and age 40.

```bash
lake build ot_kernel
python3 methods/trees/tree_certificate.py robust examples/tree_ensemble/model_lightgbm.json \
  examples/tree_ensemble/box_applicant.json --approve --check      # approved on the whole box
python3 methods/trees/tree_certificate.py monotone examples/tree_ensemble/model_lightgbm.json 0 --up --check
python3 methods/trees/tree_certificate.py monotone examples/tree_ensemble/model_lightgbm.json 1 --down --check
```

Each accepted request is a claim of [`robust-decision`](../../specs/claims/robust-decision.md) or
[`monotone-feature`](../../specs/claims/monotone-feature.md): true for the integer ensemble, with
`δ = 0`, under A3 and A11 (`specs/assumptions/`). The kernel takes about half a millisecond for
each.
