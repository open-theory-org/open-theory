# Claim cards

One card per specification (observable × domain × aggregate, `docs/language.md`). A card names
its claim types: terms of `OpenTheory.ClaimType` in `formal/core/Specs/ClaimTypes.lean`, one per
model family and check, each with its `Sound` theorem. A card about a property shared by several
families (`decision`, `monotone`) lists one claim type per family, for example `robust-decision`:
`robustRegion` (ReLU networks) and `treeRobust` (tree ensembles).

Each card starts with a TOML header (`id`, `observable`, `domain`, `aggregate`, `models`, `lean`,
`claim_types`, `assumptions`, `references`), checked by `tests/regression/check_specs.py` and, against
the elaborated Lean terms, by `tests/regression/check_spec_shapes.py`.

**The list of cards, their claim types, methods, fast checks and levels is generated:**
[../coverage.md](../coverage.md).

Planned:

| Card | Spec | Rule |
| --- | --- | --- |
| `calibration` | quantity (squared error of the predicted probability) × committed pool × `meanLe` | bounded-mean tail on the beacon sample |
| `auc` | property on (positive, negative) pairs × two pools × `meanGe` | pair-sampling tail |
| `latency-p99` | quantity × committed pool × `quantileLe` | order-statistic tail |
| `robust-accuracy` | rate of inputs whose decision is robust on a box, on a pool | `robust-decision` per item, then `pool-rate` |
