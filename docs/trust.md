# What a certificate asks you to trust

A certificate says: **this claim is true, except with probability at most δ.** This page lists
everything that sentence rests on, and only that. The objects (claim type, assumption, method) are
defined in [language.md](language.md); the levels in
[specs/protocols/assurance-levels.md](../specs/protocols/assurance-levels.md).

Running example: the credit model's approval of Alice is robust on her box
(`robust-decision`, `δ = 0`).

## 1. The chain from the world to the answer

```
the world                 the deployed model, the data, the beacon, the labels
   │  assumptions         A3: the certified model is the deployed one; A11: the LightGBM translation
   ▼
the Lean objects          law, observable, domain, model of the claim type
   │  the statement       ClaimTypes.treeRobust: "the decision is c on every x of the box"
   ▼                      (a human reads that it says what the card says)
the claim type            its Sound theorem, proved once and checked by the kernel
   │  the proof
   ▼
the acceptance            "robustCertK … = true"
   │  the run             who evaluated the check on this certificate: the kernel, or compiled code
   ▼
the answer                accepted: the claim holds, except with probability δ
```

Each arrow can fail in its own way, and each is covered by exactly one of three questions.

## 2. Three questions, answered separately

| Question | Answered by | Values | Who decides it |
| --- | --- | --- | --- |
| **Is the method proved?** Does an accepted check imply the claim? | the method's **level** | `verified`, `specified`, `experimental` | derived by CI from the catalog's links |
| **Was this check run by a verified executor?** | the **lane** of the run | kernel, compiled (and, if ever needed, verified machine code) | the verifier, on each run |
| **Are the Lean objects the real ones?** | the **assumptions** | A1 … A11, each bridging the law, the observable, the domain or the model | the protocol, the issuer, the auditor |

They are independent: a `verified` method run in the compiled lane under A3 and A11 is a different
statement from the same method run by the kernel. A result therefore carries all three:

> `robust-decision` · method `verified` · kernel lane · `δ = 0` · assumes A3, A11

## 3. The level: what is proved about the method

| Level | Meaning | What a wrong result needs |
| --- | --- | --- |
| **verified** | a Lean specification, a kernel-checked theorem that every accepted check meets it, exact arithmetic, a conformance test | a bug in the Lean kernel, or a false assumption |
| **specified** | the result is defined in Lean, but the code that computes it is not proved (floating point, an unverified library) | a bug in that code |
| **experimental** | no formal specification: evidence, not a guarantee | anything |

In a `verified` method the producer (Python) is untrusted: a bug in it can make the kernel reject
an honest certificate, never accept a false one. The one exception is a producer that translates
the model itself (the LightGBM reader): a bug there gives a true claim about a different model,
which is why that translation is an assumption (A11) and is checked by re-running it.

## 4. The lane: who ran the check

| Lane | What runs | What you trust in addition to the proof | Time | Label |
| --- | --- | --- | --- | --- |
| **Kernel** (`ot_kernel`) | the Lean kernel evaluates the check (`robustCertK`) on the certificate | the Lean kernel and GMP | MLP 0.2–2 ms; trees 4 ms (10) to 0.2 s (500) | `verified` |
| **Compiled** (`ot_check`, `--compiled`) | the same Lean function, compiled to machine code | also the Lean compiler, the C compiler, the runtime | microseconds | "compiled check, not verified: trusts the Lean compiler" |
| **Verified machine code** (not built) | a checker compiled by a verified compiler (CakeML, as `cake_lpr` does for SAT proofs) | that compiler, and a proof in its logic matching ours | microseconds | — |

Lean has no verified compiler, so the kernel is the only executor that Lean itself verifies.
What protects the compiled lane today: it calls the very functions whose soundness is proved
(`poolCheck`, `robustCert`, `MLP.check`); CI runs both lanes on honest, tampered and random
certificates and fails on any disagreement (`ot_kernel --compare`); and any compiled result can be
re-checked by the kernel on demand.

**Fast and fully verified** is reached from both sides:

| Step | What it does | Effect |
| --- | --- | --- |
| A. One fast check per claim type | the check is a handful of big-integer operations (the kernel runs GMP at compiled speed; every other step costs about 1.5 µs), proved equal to the reference check | the kernel lane becomes sub-millisecond: fast **and** verified. Done for the MLP (2 ms for 100k parameters); measured for every check in [benchmarks.md](benchmarks.md); next, trees (`docs/PLAN.md`) |
| B. Close the gaps between the lanes (done) | one Lean decoder from the certificate's numbers to the check's arguments, shared by both lanes; the claim the verifier means is compared with what that decoder reads (`ot_kernel --show`), so the Python encoder and the Lean decoder check each other on every run; a theorem that the compiled entry runs the kernel's check (`runRobust_eq`, `runMonotone_eq`; the pool entries call `poolCheck` itself) | the compiled lane is "verified source, unverified compilation": the compiler is its only extra trust |
| C. Verified machine code | only if a user requires it | removes the compiler from the trust |

## 5. The assumptions: why the Lean objects are the real ones

For the statistical claim types, what is proved, what the kernel computes from the beacon and
what stays an assumption is detailed in [statistics.md](statistics.md).


The proof is about the objects in Lean. Each assumption bridges one of them to the world
(`specs/assumptions/`):

| Bridges | Lean object | Assumptions | How it is discharged |
| --- | --- | --- | --- |
| `law` | the law of the evidence | A1 IID, A2 model fixed before the sample, A5 uniform beacon, A6 seed after commitment, A7 all attempts counted | the sampling protocol: commit, then a public beacon; timestamps; a transparency log |
| `observable` | what the property tests | A4 labels, A9 gold labels | who labels, and when (after sampling, independently of the issuer) |
| `domain` | the population | A8 the pool is the traffic, A10 each pool is its group, A12 the checked items are the committed ones | signed receipts with inclusion proofs; how groups were recorded; Merkle inclusion under a collision-resistant hash |
| `model` | the model the claim is about | A3 the deployed model, A11 the LightGBM translation | a hash of the model, attestation; re-running the deterministic translation |

An assumption is never a hidden hypothesis: a certificate lists every one it uses, and CI checks
that each names its bridge. A false assumption does not make the proof wrong; it makes the claim
about something other than the world.

## 6. What each failure would cause

| If this fails | Effect | Caught by |
| --- | --- | --- |
| the statement does not say what the card says | a true claim, but not the one intended | a human reading the statement (required before it enters `formal/`); `check_spec_shapes.py` for its shape |
| the Lean kernel | a false acceptance in every lane | the kernel's own track record; a second, independent checker (planned) |
| the compiler (compiled lane only) | a false acceptance in that lane | differential testing in CI; re-checking by the kernel |
| a producer in a `verified-checker` method | an honest certificate rejected | conformance tests |
| the model translation (A11) | a true claim about another model | re-running the translation; the semantic test in `tree_check.py` |
| an assumption | the guarantee does not apply to the world | the protocol and whoever audits it |

## 7. In one line per claim type

| Claim type | Level | Lanes | δ | Assumptions (bridges) |
| --- | --- | --- | --- | --- |
| `robust-decision` (trees), `monotone-feature` | verified | kernel, compiled | 0 | A3, A11 (model) |
| `heldout-error` | verified | kernel (`ot verify`) | δ | A1, A2 (law), A4 (observable), A3 (model) |
| `pool-rate` | verified | kernel, compiled | `(1 + N/2²⁵⁶)ⁿ δ` | A5, A6, A7 (law), A12 (domain) |
| `judged-rate` | verified | kernel, compiled | sum of parts | A5, A6, A7 (law), A9 (observable), A12 (domain) |
| `rate-gap`, `rate-ratio` | verified | kernel, compiled | sum of parts | A5, A6, A7 (law), A10, A12 (domain) |
| `occam-code-error`, `pacbayes-error` | verified | kernel | stated per claim type | A1 (law), A4 (observable), A3 (model); A2 (law) for PAC-Bayes |
| `robust-decision` (networks) | theorem, no method yet | — | 0 | A3 (model) |
| `mlp-exact` | experimental | kernel, compiled | — | A3 (model) |

The authoritative versions are generated: [catalog/README.md](../catalog/README.md) (levels and
what proves what) and [specs/coverage.md](../specs/coverage.md) (claims by model, property and
domain).
