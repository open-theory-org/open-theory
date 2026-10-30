# Unforgeable generalization bound (demo)

A model vendor claims: **"with 95% confidence, my network's error on new data is at most 6.06%."**
Here that claim is a theorem, `DemoCert.certificate`, about the network's **population** error.
The Lean proof checker accepts it only if it is true. Nobody has to trust the vendor, the
training code, or us. Only the Lean kernel is trusted.

## Run

```bash
./examples/certified_accuracy/run_demo.sh          # 5 scenarios in parallel, about 2 minutes
python3 examples/certified_accuracy/certify.py     # honest claim only, about 1.5 minutes
```

Requires the built `OpenTheory` library (`lake build`). Generated Lean files and logs go to `out/`.

## As a certificate anyone can check

```bash
interfaces/cli/ot certify heldout examples/certified_accuracy/model/pacbayes_digits64.json --out /tmp/cert
interfaces/cli/ot verify /tmp/cert
```

The same claim as a v0.1 bundle (data only, no Lean source). `ot verify` writes the theorem from the
`heldout-error` template and checks it with the kernel. The conformance suite
(`tests/conformance/heldout_verify.py`) covers 14 forgeries.

## What happens

| Scenario | Claim | Result |
| --- | --- | --- |
| 1. Honest | 16 errors on 397 held-out examples, error ≤ 6.06% | **Accepted**: theorem proved |
| 2. Lie about errors | "only 10 errors" | **Rejected**: the kernel re-runs the network and finds the count false |
| 3. Over-claim the bound | "error ≤ 3%" from the same data | **Rejected**: P(Bin(397, 0.03) ≤ 16) > 5%, so the tail inequality is false |
| 4. Tamper with test data | change one held-out label | **Rejected**: the error count no longer matches |
| 5. Tamper with the model | change one weight | **Rejected**: same |

## Why it can't be faked

1. **The kernel recomputes everything.** The network (64–16–10, 1,210 two-bit weights) is
   evaluated by the Lean kernel on all 397 examples in exact integer arithmetic
   (`decide +kernel`, no `native_decide`, no floating point).
2. **The statistics are proved, not asserted.** The step from "16 errors in 397" to "population
   error ≤ 6.06% with 95% confidence" is the exact binomial (Clopper–Pearson) tail,
   proved in `formal/core/Verification/Statistical/BinomialTail.lean` for any data distribution.
   For a single fixed model this is the tightest valid bound; no looser approximation is used.
3. **Only standard axioms.** No `sorry`; checked by `verifier/backends/formal/audit_axioms.lean`.

## What it does NOT prove (say this out loud)

- **The held-out examples are independent and were not used for training.** This is the one
  assumption. It is a protocol assumption, enforced by committing to (hashing) the test set before
  training. It is not a mathematical fact.
- **The bound is about data from the same distribution.** It does not cover distribution shift.
- **It is about this exact network.** Any change to the weights needs a new certificate (scenario 5).

## Scaling (for questions)

- The same pipeline checked a 203,530-parameter 784–256–10 network at about 0.28 s per example
  (`formal/core/Verification/Computation/QuantizedMLPPacked.lean`).
- The same method certifies **any** model's outputs whenever each output's correctness is
  machine-checkable (answers to verifiable questions, code that passes tests, reconciled numbers),
  including generated outputs of large models evaluated outside the kernel and committed by hash.
