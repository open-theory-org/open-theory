# verifier/: independent checking

The trusted core is the **Lean kernel**. Everything here is a thin layer that decides what to run and reports the result.

| Folder | Today |
| --- | --- |
| [core/](core/) | `ot verify` engine: protocol steps 1–6 for `heldout-error` v0.1 |
| [backends/formal/](backends/formal/) | [`audit_axioms.lean`](backends/formal/audit_axioms.lean): axiom and `sorry` audit of every OpenTheory declaration |
| [backends/statistical/](backends/statistical/) | empty. Statistical checks are Lean theorems today (`formal/core/Specs/`) |
| [backends/neural/](backends/neural/) | empty |
| [backends/zk/](backends/zk/) | empty. Will call the zkVM vendor's verifier |
| [backends/runtime/](backends/runtime/) | empty |
| [attestations/](attestations/) | empty. Planned: Sigstore signatures and Rekor/SCITT log checks. Use them as they are; build nothing in-house |
