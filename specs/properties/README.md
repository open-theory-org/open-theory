# Properties

| Property | Formal basis today | Status |
| --- | --- | --- |
| Accuracy / error rate | `formal/core/Specs/` (`HeldOut`, `QuantizedMLP/Occam`, `QuantizedMLP/PACBayes`) | verified |
| Local robustness (ε-ball) | none | planned: integer interval bound propagation on `QuantizedMLP` |
| Head-ablation fidelity | `formal/core/Theory/Function/AttentionAblation.lean` | theorem only, no method yet |
| Causal effects | none | `formal/core/Theory/Agents/` is empty |
| Agent constraints | none | `formal/core/Theory/Agents/` is empty |
