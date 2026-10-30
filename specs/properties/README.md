# Properties

| Property | Formal basis today | Status |
| --- | --- | --- |
| Accuracy / error rate | `formal/core/Specs/` (`HeldOut`, `QuantizedMLP/Occam`, `QuantizedMLP/PACBayes`) | verified |
| Local robustness (ℓ∞ ball) | `formal/core/Scopes/OnRegion.lean` (`certify_sound`, `robust_of_certify`) over `Models/Exact` (`Net.box_sound`) | theorem and kernel check for every network built from exact `linear` / `relu` primitives; no method, catalog entry or conformance test yet, so no level |
| Head-ablation fidelity | `formal/core/Theory/Function/AttentionAblation.lean` | theorem only, no method yet |
| Causal effects | none | `formal/core/Theory/Agents/` is empty |
| Agent constraints | none | `formal/core/Theory/Agents/` is empty |
