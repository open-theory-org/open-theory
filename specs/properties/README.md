# Properties

One card per observable (`docs/specs.md`): a property, a yes/no test of a model on one input, or a
quantity, a value in `[0, 1]`. Each card starts with a TOML header (`id`, `kind`, `object`, `test`,
`lean`, `references`) checked by `tests/regression/check_specs.py`.

| Observable | Core object | Card |
| --- | --- | --- |
| `predicts` | learned function | [predicts.md](predicts.md) |
| `exact-output` | learned function | [exact-output.md](exact-output.md) |
| `wrong` | statistical predictor | [wrong.md](wrong.md) |
| `event` | behavior (black box) | [event.md](event.md) |

Which claims use them, with which scope and at which level: [../coverage.md](../coverage.md).
Planned: monotonicity, fairness between inputs, calibration, equivalence of two models, monitor
soundness.
