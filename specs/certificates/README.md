# Certificate formats

## v0.1 (current): a bundle directory

```text
bundle/
  certificate.json   claim, file digests, assumptions, pins      (schema: schema.json)
  model.json         the model as data (quantized-mlp: architecture + integer codes)
  heldout.json       the evidence (held-out rows)
```

- **No Lean source in the bundle.** `ot verify` writes the Lean statement from the claim template (`OpenTheory.HeldOut.Claim`) and the hashed data, then runs the kernel. A producer cannot swap in a weaker theorem or inject Lean code.
- **The level comes from `catalog/guarantees/`,** not from the certificate. The certificate must list every assumption of that guarantee.
- Produce with `ot certify heldout <artifact> --out bundle/`. Check with `ot verify bundle/`.

## v0 (the demo)

The demo writes a generated Lean file and runs `lake env lean` on it ([`examples/certified_accuracy/certify.py`](../../examples/certified_accuracy/certify.py)). It is kept as a demonstration. v0.1 supersedes it.
