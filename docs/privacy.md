# Showing a result without the model

How a certificate can be checked by someone who must not see the model or the data, using
existing systems (no new cryptography, [PLAN.md](PLAN.md) §7), and where this fits in what a
result asks you to trust ([trust.md](trust.md)). Read §2–3 first for private *rates* (accuracy, error, fairness).

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

## 2. Private claims about meaning: what exists

Most zero-knowledge ML proves a *computation* (an inference, an accuracy on a dataset). The
question here is whether anyone proves what that computation *means*: a rate on the population,
with a sample the prover could not choose.

| Work | Proved in zero knowledge | Sample chosen after the commitment, verifiably? | Population bound? |
| --- | --- | --- | --- |
| zkDT [@zhang2020zkdt] | tree predictions and accuracy on a dataset | no | no: accuracy on that dataset |
| Kang et al. [@kang2022scaling] | quantized MobileNet inference (Halo2); the verifier computes accuracy from revealed outputs | partly: model and test-set hash committed first, but the prover picks the subsets | Clopper–Pearson and Hoeffding size the sample, computed in the clear, not proved |
| FairProof, Confidential-PROFITT [@yadav2024fairproof; @shamsabadi2023profitt] | fairness of a network; fair tree training | no | no: per input or at training |
| PANDA [@zhong2026panda] | local robustness from CROWN bounds (the evaluated build is not zero knowledge) | no | no: per input |
| ZK-SR117 [@uddin2026zksr117] | demographic-parity gap and calibration error (EZKL), logistic regression | designed, not implemented | no |
| Luck et al. [@luck2026certified] | none: an analysis of nine such schemes, all gameable by forging data around a public audit set | the proposed fix (commit, then sample); in Python, not in zero knowledge | yes, a concentration theorem in the paper, not machine-checked |

A private claim about meaning needs three things at once:

1. **the sample is drawn after the commitment, from public randomness** (otherwise the attack of
   Luck et al. applies);
2. **a population bound whose derivation is machine-checked** (otherwise the step from "k errors
   in n" to "error rate ≤ ε, except with probability δ" is trusted);
3. **zero knowledge** for the model and the data.

Each exists somewhere; no work found does all three (searched 2026-11-02 from abstracts and
summaries, not exhaustive). OpenTheory already has 1 (`pool-rate`: RFC 3161 timestamp, drand
beacon, Merkle commitments) and 2 (`Specs.PoolSample`, `Claim.of_poolCheck`). The missing piece is 3.

## 3. The quickest private certificate: prove the count, check the bound in the clear

In `pool-rate` almost everything is already public. Only the sampled items, and the model if it
is evaluated, need hiding:

| Step | Public or private | Checked by | Exists |
| --- | --- | --- | --- |
| the commitment is timestamped before the beacon round | public | `pool_rate.py` step 1 (`rfc3161.py`) | yes |
| the beacon round and its signature | public | `pool_rate.py` step 2 (`drand.py`) | yes |
| blocks `bᵢ` and indices `jᵢ = bᵢ mod N` | public: they say *which* items, not what they contain | `derive_blocks`; the kernel rechecks `jᵢ = bᵢ mod N` | yes |
| item `jᵢ` is in the committed pool (A12) | **private** item and path, public root | today `merkle.py`; **the zkVM guest** | to build |
| the bit of position `i`: output = label (`Drawn.bit`) | **private** | today the kernel; **the zkVM guest** | to build |
| the count and the tail: `d · P(Bin(n, a/b) ≤ k) ≤ 1` | public: the bits `x`, `n`, `k`, `a/b`, `δ = 1/d` | the kernel, `poolCheck` unchanged | yes, `verified` |

So the zero-knowledge part is small. For each `i`, the guest checks the Merkle inclusion of the
private item at the public index, computes its bit, and outputs `x`. Its public output (the
journal) is `(root, N, round, n, x)`. The verifier checks the receipt, runs steps 1–3 as today and
then `ot_kernel` on `poolCheck x n l k a b d`.

Two variants:

| Variant | The guest also | Hides | The claim |
| --- | --- | --- | --- |
| **Logged decisions** (`pool-rate` as it is) | nothing: each pool item already holds the model's recorded output and its label | the production data | the error rate on the committed traffic ≤ `a/b`, except with probability `δ` (A8: the pool is the traffic) |
| **Committed model on committed data** | reads the private model, outputs `SHA-256(model)` in the journal (and in the commitment before the beacon), computes `aᵢ = model(item jᵢ)` | the model and the data | the same rate for *that* model; generalization to a distribution adds A1 (the pool is drawn IID from it) |

What `x` reveals: which sampled positions are errors, not what the items contain. If that is too
much, the guest outputs only `k`, and the kernel needs a tail-only check (`d · tailFast n k a b ≤ bⁿ`),
a small new function whose soundness follows from the existing theorem (statement to review).

**The trust, stated exactly.** The bound is `verified`, by the kernel. The bits come from a
receipt of a Rust guest that re-implements `Drawn.bit`, RFC 9162 inclusion and, in the second
variant, the tree evaluation of `Checks.Tree`, none of it proved equal to the Lean definitions.
Label: *count: zkVM receipt, guest not verified; bound: verified*. This is the same kind of gap as
A11 (a translation) and is covered the same way: differential tests of the guest (run without
proving) against `ot_kernel` on the same inputs, public test vectors in CI, and later route B,
which compiles the Lean functions themselves into the guest.

**Effort (estimates).** Logged decisions: about 2–4 days (a guest of about 150 lines of Rust,
using the zkVM's SHA-256 acceleration; host; `verifier/backends/zk/`; the example in
`examples/private_verification/`, already planned for it). Committed model with tree ensembles:
3–5 more days. Proving cost is unmeasured; for `n` = 1,000–5,000 items with about 20 hashes each
it is likely seconds to minutes on a laptop, to measure first.

## 4. What a private result must contain

Every route, including §3, produces the same **public statement**, and only it leaves the private side:

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

## 5. Three routes that reuse what exists

| | A. Enclave (TEE) | B. zkVM running the compiled check | C. zkVM running a Lean kernel |
| --- | --- | --- | --- |
| **What runs privately** | `ot_kernel`, unchanged: the kernel lane | the Lean functions of `ot_check`, compiled to RISC-V | an independent Lean kernel checking `check args = true` |
| **Exists** | AWS Nitro Enclaves [@awsnitro], AMD SEV-SNP, Intel TDX; open-source attestation verifiers | RISC Zero [@risczero] (Rust guests, with a C/C++ toolchain for rv32im), SP1 [@sp1]; Lean compiles to C | nanoda\_lib [@nanoda] (Rust, checks lean4export, Nat extension), Lean4Lean [@carneiro2024lean4lean] |
| **What the regulator checks** | the attestation: signed by the vendor, enclave image hash (PCR0) = our reproducible build, `user_data` = hash of the statement | the receipt: the zkVM verifier, image ID = our guest build | the receipt, image ID = the kernel's build, environment hash = our `Checks` export |
| **Trusted in addition** | the hardware vendor and its signing key | the zkVM (circuits, cryptography), the Lean and C compilers | the zkVM and that second kernel |
| **Lane label** | kernel, in an attested enclave: method stays `verified` | "compiled check, not verified", in a zkVM | kernel lane, in a zkVM (a second, independent checker) |
| **Cost per check** | the kernel's: 0.1 ms to 0.2 s | proving: seconds to minutes; verifying: ms | proving: likely minutes or more; unmeasured |
| **Effort** | about 1–2 weeks | about 3–6 weeks, with porting risk | research: months |

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

§3 is this route restricted to the private steps, with a Rust guest instead of compiled Lean.

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

nanoda\_lib already checks Lean 4 exports in Rust, with a Nat extension, and Rust is what zkVMs
run best. The idea: export the `Checks` environment once (it is public; only the arguments are
private), and prove inside the zkVM that a second kernel accepts `check args = true` for those
arguments. That would give a private result with the kernel lane's meaning, and a second
independent checker, which [trust.md](trust.md) §6 already plans. Unmeasured; research.

## 6. What does not fit, and why

| System | What it proves | Why it does not replace the routes above |
| --- | --- | --- |
| EZKL [@ezkl] | ONNX inference in Halo2, on quantized weights | a second implementation of the computation, not our proved check; a 2026 study for fair-lending metrics could not compile a 10-tree XGBoost model and used logistic regression [@uddin2026zksr117] |
| zkAudit [@waiwitlikhit2024zkaudit] | audits on committed models and data | the computation, not its meaning (sampling and bound not established here) |

These, and the works of §2, are prior art to use as building blocks or contrast: none runs our
proved checks, so none can replace them.

## 7. Where it fits

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
| the bank milestone ([PLAN.md](PLAN.md) §6) | its last step, "binding and privacy": the private count of §3 first, then route A |

## 8. What a private result does not hide or prove

- The statement is public: the box, the decision, the rate, the sample size. A claim can reveal
  something about the model (a box on which it approves).
- Sizes and timings can leak the number of trees or features unless padded.
- An attestation or receipt proves the check ran on *the committed* model; that the committed model
  is the one in production is still A3, discharged only if the serving system is attested too.

## 9. Recommended order

1. The private count of §3, logged-decisions variant, in `examples/private_verification/`:
   the first private claim with a sample drawn after the commitment and a machine-checked bound.
2. The committed-model variant on tree ensembles, with differential tests against `ot_kernel`.
3. The statement format and the public/private split for every check (shared by all routes).
4. Route A end to end on the credit-model report: trees, monotonicity, `pool-rate`.
5. Route B: compile the Lean functions into the guest, which removes the guest gap of §3.
6. Route C as research, with the second-checker work.
