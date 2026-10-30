# cli: `ot` (short for opentheory)

```bash
interfaces/cli/ot certify heldout examples/certified_accuracy/model/pacbayes_digits64.json --out /tmp/cert
interfaces/cli/ot verify /tmp/cert            # exit 0 accept, 1 reject, 2 error
interfaces/cli/ot verify /tmp/cert --json     # machine-readable report
```

Run it from an OpenTheory checkout after `lake build`. To call it as `ot`, add `interfaces/cli` to your `PATH`.
