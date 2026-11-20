# Showing a result without the model

How a certificate can be checked by someone who must not see the model or the data, using
existing systems (no new cryptography, [PLAN.md](PLAN.md) §7), and where this fits in what a
result asks you to trust ([trust.md](trust.md)).

Running example: the bank's credit model approves Alice on her box (`robust-decision`, trees,
`δ = 0`). The regulator must learn exactly this:

> `robust-decision` · trees · box `B` · decision `approve` · model commitment `h` · method `verified` · accepted

and nothing about the trees.

## 1. The gap today

| What the verifier receives | What it reveals |
| --- | --- |
| the request `ot_kernel robust …`: base score, trees, leaf margins, box, decision | **the whole model** (every split and leaf) |
| a `pool-rate` certificate: the sampled items and their Merkle paths | the sampled production data |
| the model hash (A3) | nothing, but alone it proves nothing either |

The kernel must read the model to check the claim, so *whoever runs the kernel sees the model*.
Privacy means moving the run to a place the regulator trusts but cannot look into, and getting
back only the statement and the answer, bound to commitments.

## 2. What a private result must contain

Every route below produces the same **public statement**, and only it leaves the private side:

| Field | Example | Why |
| --- | --- | --- |
| check and version | `Tree.robustCertK`, the `Checks` build hash | which proved function was run |
| public arguments | box `B`, decision `approve` | the claim itself, as `ot_kernel --show` decodes it |
| commitments to the private arguments | `h = SHA-256(trees, margins)`, data Merkle root | A3 (this is the deployed model) and A12 (these are the committed items) |
| beacon round | drand round `r` | A5, A6 for the statistical claims |
| answer | `true` | the acceptance |

The commitment has to be computed **inside** the private side, over the same bytes the decoder
reads; otherwise the proof could be about one model and the hash about another. Each check needs
a declared split of its arguments into public and private parts (to build: one table next to
`Checks.Registry`).

## 3. Three routes that reuse what exists

|                               | A. Enclave (TEE)                                                                                                               | B. zkVM running the compiled check                                                                     | C. zkVM running a Lean kernel                                                                     |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------- |
| **What runs privately**       | `ot_kernel`, unchanged: the kernel lane                                                                                        | the Lean functions of `ot_check`, compiled to RISC-V                                                   | an independent Lean kernel checking `check args = true`                                           |
| **Exists**                    | AWS Nitro Enclaves [@awsnitro], AMD SEV-SNP, Intel TDX; open-source attestation verifiers                                      | RISC Zero [@risczero] (Rust guests, with a C/C++ toolchain for rv32im), SP1 [@sp1]; Lean compiles to C | nanodalib [@nanoda] (Rust, checks lean4export, Nat extension), Lean4Lean [@carneiro2024lean4lean] |
| **What the regulator checks** | the attestation: signed by the vendor, enclave image hash (PCR0) = our reproducible build, `user_data` = hash of the statement | the receipt: the zkVM verifier, image ID = our guest build                                             | the receipt, image ID = the kernel's build, environment hash = our `Checks` export                |
| **Trusted in addition**       | the hardware vendor and its signing key                                                                                        | the zkVM (circuits, cryptography), the Lean and C compilers                                            | the zkVM and that second kernel                                                                   |
| **Lane label**                | kernel, in an attested enclave: method stays `verified`                                                                        | "compiled check, not verified", in a zkVM                                                              | kernel lane, in a zkVM (a second, independent checker)                                            |
| **Cost per check**            | the kernel's: 0.1 ms to 0.2 s                                                                                                  | proving: seconds to minutes; verifying: ms                                                             | proving: likely minutes or more; unmeasured                                                       |
| **Effort**                    | about 1–2 weeks                                                                                                                | about 3–6 weeks, with porting risk                                                                     | research: months                                                                                  |

Every route reuses the same proofs: what an accepted check means is the `Sound` theorem of its
claim type, unchanged. The routes differ only in **who ran the check** and what that adds to the
trust, which is exactly the lane of [trust.md](trust.md) §4.

### A. Enclave: the shortest route, and the only one that keeps the kernel

What exists and is reused:

- `ot_kernel` and the `Checks` oleans, as they are. The enclave runs the kernel lane itself.
- `verifier/core/merkle.py` and `verifier/attestations/drand.py` for the data root and the
beacon round; `ot_kernel --show` for the public arguments.
- Open-source verifiers of Nitro attestation documents (COSE signature, chain to the AWS root,
PCR comparison) to wrap or reproduce with standard libraries.

What to build:

1. An enclave image: the Lean toolchain's runtime, `ot_kernel`, the `Checks` build; a small

   wrapper that reads a request over vsock, hashes its private part, runs `ot_kernel --stdin`
    and asks the enclave for an attestation with `user_data = SHA-256(statement)`.
2. A **reproducible** image build, so the regulator can recompute PCR0 from this repository. This

   is the hard part of the route, not the code.
3. `verifier/attestations/nitro.py`: verify the document, compare PCR0 with the published build,

   recompute the statement hash.
4. The public/private argument split and the statement format (shared with routes B and C).
5. A test mode with a local key standing in for the vendor's, so that CI exercises the whole path

   without hardware.

What it needs from you: an AWS account with a Nitro-capable instance for the end-to-end test.

### B. zkVM with the compiled check: succinct, but the compiled lane

What exists:

- Lean emits C (the `:c` facet of a module, e.g. `lake build Checks.Tree:c`); a public sample runs Lean-generated C in a RISC Zero
guest; `lean2zkvm` aims at this but is a small, early project.
- The checks are core-only (`Checks` imports only Lean's core), so the guest needs the Lean
runtime but not Mathlib.

What to build and what is uncertain:

1. Cross-compile the Lean runtime (C++) to rv32im without threads, and without GMP (Lean has a

   built-in big-integer fallback; to confirm on our toolchain). This port is the main risk.
2. Choose the **reference** checks, not the packed ones. Packing (Kronecker products, megabit

   integers) saves kernel *steps*, which cost 1.5 µs each in the kernel and almost nothing in
    compiled code; in a zkVM, the cost is cycles, and megabit multiplications are expensive. Both
    are proved to give the same answer, so the choice changes cost, never meaning.
3. Measure cycles for trees, linear models and `pool-rate`; wrap the receipt verifier in

   `verifier/backends/zk/` (today an empty placeholder for exactly this).

A shortcut, rewriting a check in Rust for the guest, takes days but adds an unproved program;
[PLAN.md](PLAN.md) Phase 5 already names that gap and asks for differential testing against
`ot_kernel --compare`. It should be labelled as such, never as `verified`.

### C. A kernel inside a zkVM: the long-term route

nanodalib already checks Lean 4 exports in Rust, with a Nat extension, and Rust is what zkVMs
run best. The idea: export the `Checks` environment once (it is public; only the arguments are
private), and prove inside the zkVM that a second kernel accepts `check args = true` for those
arguments. That would give a private result with the kernel lane's meaning, and a second
independent checker, which [trust.md](trust.md) §6 already plans. Unmeasured; research.

## 4. What does not fit, and why

| System | What it proves | Why it does not replace the routes above |
| --- | --- | --- |
| EZKL [@ezkl] | ONNX inference in Halo2, on quantized weights | a second implementation of the computation, not our proved check; a 2026 study for fair-lending metrics could not compile a 10-tree XGBoost model and used logistic regression [@uddin2026zksr117] |
| zkDT [@zhang2020zkdt] | tree predictions and accuracy, in zero knowledge | accuracy on a dataset, not a bound proved to follow from it; research code |
| zkAudit [@waiwitlikhit2024zkaudit] | audits on committed models and data | the same: the computation, not its meaning; and fixed audit sets can be gamed [@luck2026certified] |

They are the closest prior art and useful as contrast. The ZK-SR117 study reports that its
sampling-nonce protocol is designed but not implemented end to end; here the
commit-then-beacon protocol exists and its bound is proved (`pool-rate`, A2, A5, A6).

## 5. Where it fits

```
the bank (private side)                        the regulator (public side)
  model, data, certificate
        │
        ▼
  ┌──────────────────────────────┐
  │ enclave or zkVM              │
  │  hash private part → h       │
  │  run the proved check        │  ──statement + attestation/receipt──▶  check signature/receipt,
  │  sign or prove the statement │                                         image = our build,
  └──────────────────────────────┘                                         read the claim and h
```

| Part of the project | What changes |
| --- | --- |
| `formal/` (claims, proofs, checks) | nothing: every route runs the proved checks |
| lanes ([trust.md](trust.md) §4) | new lanes: kernel in an enclave (A), compiled in a zkVM (B), kernel in a zkVM (C) |
| assumptions | A3 is discharged by an attestation of the serving model as well as a hash; the vendor or the zkVM is lane trust, not a new assumption about the world |
| evidence ([specs/evidence/](../specs/evidence/README.md)) | the "attestation (TEE, zkVM receipt)" row moves from planned to checked |
| verifier | `verifier/attestations/nitro.py` (A); `verifier/backends/zk/` (B, C) |
| the bank milestone ([PLAN.md](PLAN.md) §6) | its last step, "binding and privacy", in route A first |

## 6. What a private result does not hide or prove

- The statement is public: the box, the decision, the rate, the sample size. A claim can reveal
something about the model (a box on which it approves).
- Sizes and timings can leak the number of trees or features unless padded.
- An attestation or receipt proves the check ran on *the committed* model; that the committed model
is the one in production is still A3, discharged only if the serving system is attested too.

## 7. Recommended order

1. The statement format and the public/private split (shared by all routes).
2. Route A end to end on the credit-model report: trees, monotonicity, `pool-rate`.
3. Route B pilot on trees with the reference check: measure cycles before committing.
4. Route C as research, with the second-checker work.
