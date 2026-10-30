# Evidence

| Evidence | Checked by | Binds |
| --- | --- | --- |
| Model as a Lean definition (integer codes) | Lean kernel | the function (A3 still needed for deployment) |
| Held-out rows inside the certificate | Lean kernel recomputes counts | the data used |
| Hash of held-out set committed before training | transparency log timestamp (planned) | A2 |
| Weights digest | hash comparison | A3 for open weights |
| Attestation (TEE, zkVM receipt) | vendor verifier (planned) | A3 for served models |

Rule: evidence that the verifier cannot recheck is labelled as an assumption, never as checked.
