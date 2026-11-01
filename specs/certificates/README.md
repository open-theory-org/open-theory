# Certificate formats

## v0.1 (current): one bundle format for every claim type

```text
bundle/
  certificate.json   format, claim, file digests, assumptions, pins     (schema: schema.json)
  <files>            the data the claim is about, each named with its sha256 in certificate.json
```

`certificate.json` always has the same top-level fields:

| Field | Meaning |
| --- | --- |
| `format` | `"opentheory-certificate/0.1"` |
| `claim` | `type` (a card of `specs/claims/`), `version`, and the claim type's parameters |
| `subject` | what the claim is about: `model` or `commitment`, as `{path, sha256}` |
| `evidence` | the data the check reads (held-out rows, beacon, sample), as `{path, sha256}`; `{}` for trees |
| `assumptions` | every assumption id the guarantee needs (`specs/assumptions/`); a missing one is a rejection |
| `pins` | the Lean toolchain and the OpenTheory commit |

**One command checks every claim type:** `ot verify bundle/`. The report starts with one line,
the same for all of them ([docs/trust.md](../../docs/trust.md)):

```
tree-robust · verified · kernel lane · δ = 0 · assumes A3-model-binding, A11-tree-translation
```

claim type · level (from `catalog/guarantees/`, never from the certificate) · lane (`kernel`, or
`compiled (not verified)` with `--compiled`) · δ · assumptions.

| Claim type | Parameters in `claim` | Files | How the kernel checks it | Produce with |
| --- | --- | --- | --- | --- |
| `heldout-error` | `k`, `p`, `delta` | `model`, `evidence.heldout` | a Lean file from the template `HeldOut.Claim`, checked by `lean` | `ot certify heldout` |
| `pool-rate` | count, bound, δ | `commitment`, `sample` | `Checks.poolCheck` (`ot_kernel`) | `ot certify pool-rate` |
| `judged-rate` | judge, audit, alarms parts | `commitment`, `sample` | `Checks.poolCheck` per part | `ot certify pool-rate` |
| `rate-gap`, `rate-ratio` | four parts, `epsilon` or `c` | two pools | `Checks.poolCheck` per part | `ot certify pool-rate` |
| `tree-robust` | `decision`, `tau`, `box` | `subject.model` (LightGBM dump) | `Checks.Tree.robustCertK` (`ot_kernel`) | `methods/trees/tree_certificate.py robust … --out` |
| `tree-monotone` | `feature`, `direction`, `box` | `subject.model` | `Checks.Tree.monotoneCertK` (`ot_kernel`) | `methods/trees/tree_certificate.py monotone … --out` |

Rules, for every claim type:

- **No Lean source and no witnesses are trusted from the bundle.** The verifier writes the Lean
  statement from the claim type (or calls its registered check), recomputes every witness it can
  (tree bounds and cuts) and checks the rest. A producer cannot swap in a weaker statement.
- **The kernel checks what the report says.** For checks that decode structured data (trees), the
  verifier compares the claim with what the Lean decoder reads the request as (`ot_kernel
  --show`), and both lanes run the same Lean decoder; `runRobust_eq` and `runMonotone_eq` prove
  that the compiled lane runs the kernel's check.
- **The level comes from `catalog/guarantees/`**, and the certificate must list every assumption of
  that guarantee.

## v0 (the demo)

The demo writes a generated Lean file and runs `lake env lean` on it ([`examples/certified_accuracy/certify.py`](../../examples/certified_accuracy/certify.py)). It is kept as a demonstration. v0.1 supersedes it.
