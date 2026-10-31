# Properties

One card per property: a yes/no test of a model on one input (`docs/specs.md`). Each card starts
with a TOML header (`id`, `object`, `test`, `lean`, `references`) checked by
`tests/regression/check_specs.py`.

| Property | Core object | Card |
| --- | --- | --- |
| `predicts` | learned function | [predicts.md](predicts.md) |
| `exact-output` | learned function | [exact-output.md](exact-output.md) |
| `zero-loss` | statistical predictor | [zero-loss.md](zero-loss.md) |
| `no-event` | behavior (black box) | [no-event.md](no-event.md) |

Which claims use them, with which scope and at which level: [../coverage.md](../coverage.md).
Planned: monotonicity, fairness between inputs, calibration, equivalence of two models, monitor
soundness.
