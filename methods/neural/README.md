# neural

| Producer | Check | Level |
| --- | --- | --- |
| [`mlp_exact_certificate.py`](mlp_exact_certificate.py) | `mlp-exact` (`formal/core/Checks/MLP.lean`): a quantized ReLU MLP outputs exactly `Y` on `x` | experimental until the soundness theorem is proved |

Producers are untrusted. Certificates are checked by `ot_kernel` (Lean kernel) or `ot_check` (compiled), from the shared registry `formal/core/Checks/Registry.lean`.

Planned: integer interval bounds with a kernel-checked soundness proof, for certified robust accuracy.
