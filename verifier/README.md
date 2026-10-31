# verifier/: independent checking

The trusted core is the **Lean kernel**. Everything here is a thin layer that decides what to run and reports the result.
Claim types with a `Bool` decision procedure (`pool-rate`, `judged-rate`) have the kernel evaluate it; its meaning
is a theorem proved once. `ot verify --compiled` runs the same definition as compiled code: faster, but it trusts the
Lean compiler, so the result is labelled separately and never `verified`.

| Folder | Today |
| --- | --- |
| [core/](core/) | `ot verify` engine: `heldout-error`, `pool-rate`, `judged-rate` v0.1 (RFC 9162 Merkle checks in `merkle.py`) |
| [backends/formal/](backends/formal/) | [`audit_axioms.lean`](backends/formal/audit_axioms.lean): axiom and `sorry` audit of every OpenTheory declaration. [`kernel_check.lean`](backends/formal/kernel_check.lean) (`ot_kernel`): the kernel lane of the fast checks: builds `check args = true` and hands it straight to the kernel, in a warm process (`--stdin`); `--compare` also runs the compiled lane and reports any disagreement. [`ot_check.lean`](backends/formal/ot_check.lean) (`ot_check`): the compiled lane, never `verified` |
| [backends/statistical/](backends/statistical/) | empty. Statistical checks are Lean theorems today (`formal/core/Specs/`) |
| [backends/neural/](backends/neural/) | empty |
| [backends/zk/](backends/zk/) | empty. Will call the zkVM vendor's verifier |
| [backends/runtime/](backends/runtime/) | empty |
| [attestations/](attestations/) | [`drand.py`](attestations/drand.py) (pinned chains, BLS), [`rfc3161.py`](attestations/rfc3161.py) (timestamps against [`tsa_roots/`](attestations/tsa_roots/)). Planned: Sigstore and Rekor/SCITT log checks. Use them as they are; build nothing in-house |
