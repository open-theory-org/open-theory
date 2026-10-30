# Verification protocol (v0.1)

1. **Pin trust roots.** OpenTheory release commit, Lean toolchain, Mathlib revision.
2. **Match the template.** The certificate theorem's type is exactly the claim type's Lean statement, with only the declared parameters filled in.
3. **Check bindings.** Recompute the evidence digests. Check transparency-log timestamps in this order: data commitment, then model, then sampling beacon. (planned)
4. **Check by level.**
   - `verified`: re-run the kernel on the certificate.
   - `specified`/`experimental`: re-run or spot-check the harness, and report the result as unverified.
5. **Audit axioms.** Run `#print axioms` on the certificate theorem. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
6. **Report.** Give the claim, the level, the assumptions (ids), the trusted components and the scope ("does not cover").

**Status (`ot verify`, `heldout-error` v0.1).**

- Steps 2, 4, 5 and 6 are implemented.
- Step 3 checks file digests only. Transparency-log timestamps are planned.
- Step 1 enforces the toolchain, but only warns on the OpenTheory commit until the first tagged release.

Conformance: `tests/conformance/heldout_verify.py`.
