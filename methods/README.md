# methods/: producing evidence

Producers are **untrusted**. A method is only as strong as its level in [`catalog/methods/`](../catalog/), and
CI rejects any file here that has no manifest.

| Folder | Today |
| --- | --- |
| [statistical/](statistical/) | **verified**: binomial held-out bound search, quantized-MLP certificate exporters (Occam, PAC-Bayes) |
| [trees/](trees/) | **verified**: robustness and monotonicity certificates for tree ensembles (LightGBM) |
| [neural/](neural/) | empty. Planned: integer interval bound propagation (IBP) on `QuantizedMLP` (verified-checker) |
| [whitebox/](whitebox/) | empty. Planned: probes, activation patching, circuit faithfulness (experimental → rate claims) |
| [evaluations/](evaluations/) | empty. Planned: Inspect AI harness, behavioural rate claims |
| [causal/](causal/) | empty |
| [runtime/](runtime/) | empty. Planned: agent policy monitors |
| [zk_proving/](zk_proving/) | empty. Planned: zkVM receipts for private error counts |
