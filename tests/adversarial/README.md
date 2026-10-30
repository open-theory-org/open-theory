# Adversarial tests

Current attacks, all in [`../conformance/certified_accuracy.sh`](../conformance/certified_accuracy.sh):

- false error count;
- a tighter bound than the data supports;
- a tampered held-out label;
- a tampered weight.

Planned attacks, with the verifier v0.1:

- a theorem whose type is weaker than the claim template;
- `native_decide` or extra axioms;
- a certificate bound to a different toolchain or OpenTheory commit;
- reordered transparency-log timestamps.
