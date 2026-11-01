# Proved once, checked in a millisecond

How a certificate is made fast without adding anything to what is trusted. The guarantee is
always the same (`Sound`, [language.md](language.md)); this page is about the *check* the Lean
kernel runs on each certificate, and how to make it take well under a millisecond while staying
`verified` ([trust.md](trust.md)). Measured times: [benchmarks.md](benchmarks.md).

Running example: the bank's credit decision for Alice, robust on her box, from a linear score
(`robust-decision`, [examples/linear_model/](../examples/linear_model/)).

## 1. The constraint: what the kernel pays for

Every certificate is checked by the Lean kernel evaluating one proposition, `check args = true`.
Its cost has three parts, all measured on this repository:

| Cost | Size | What drives it |
| --- | --- | --- |
| a reduction step (unfolding a definition, matching a constructor, one recursion step) | about **1.5 µs** | the number of steps, whatever the numbers in them |
| a big-integer operation (`Nat.add`, `mul`, `land`, `shiftRight`, `ble`, `beq`, `pow`) | GMP speed, **nanoseconds per machine word** | the size of the numbers, at compiled speed |
| setting up a request (building and type-checking its terms) | about **0.1 ms**, plus a few µs per list element | the size of the request |

So a check costs about `1.5 µs × steps + GMP time + 0.1 ms`. **Under a millisecond means a few
hundred steps**, whatever the size of the model or of the sample. A check that walks a tree node
by node, or a sample item by item, pays about 25 steps (40 µs) per node or item, and cannot get
there; a check that is a fixed number of big-integer relations can, at any size.

Three habits keep the step count down, learned the hard way (all in `formal/core/Checks/`):

- recurse with the recursors (`Tree.rec`, `List.rec`, `Nat.rec`), not structural recursion;
- compare and branch with direct primitives (`Nat.ble`, `cond`, integers by cases), not `if` on a
  `Bool`, `decide` or `Option.bind`, whose instances cost dozens of unfoldings each;
- give the kernel literals, never terms it must evaluate twice.

Each such kernel form is proved equal to a plain reference form (`robustK_eq`, `poolSampleK_eq`, …),
which the soundness proof uses and the compiled lane runs (`runRobust_eq`, …).

## 2. Three principles

### Verify, don't recompute: intermediate quantities

The producer computes whatever is expensive to find; the certificate carries the result as an
**intermediate quantity**; the kernel checks only that it is consistent. Any value that passes the
check gives a true claim, so these values are untrusted:

| Check | Intermediate quantity (from the producer) | What the kernel checks |
| --- | --- | --- |
| held-out error | the tightest bound `p`, found by bisection | one integer tail inequality |
| pool rate, large sample | a Chernoff witness `t = u/v` | one polynomial inequality |
| tree robustness | a bound per tree | every reachable leaf is within its bound |
| tree monotonicity | a cut per split | the reachable leaves on each side of the cut |
| exact MLP output | each layer's dot products, pre-activations and activations | each layer's relation to the next |
| beacon sample | (none needed: the blocks are the beacon's) | index = block mod N, the outcomes, the count |

This is what lets a white-box check avoid recomputing the model: it checks the model's relations
on the intermediate quantities, layer by layer or tree by tree.

### Move whole vectors: packing

A vector of numbers is one big integer, each number in a slot of fixed width. One GMP operation
then acts on every slot at once:

| Packed operation | Replaces | Proved by |
| --- | --- | --- |
| one product of two packed vectors (Kronecker substitution [@harvey2009kronecker]) | all `n` dot products of a layer | `Kronecker.kronecker_dot`: slot `d − 1` of the product is the dot product, if no slot overflows |
| `x &&& mask = 0` | a bound check on every slot | `Kronecker.slot_lt_of_land_eq_zero` |
| an addition with guard bits | a comparison in every slot | the guard bit of slot `i` is set iff its value is ≥ the threshold |
| a population count by halving | counting the set bits | `PoolRate.popTree_eq` |

With packing, the step count no longer grows with the vector's length; only GMP's time does, at
nanoseconds per word. The exact MLP check already works this way: 2 ms for 101,770 parameters,
0.4 ms for 1,210.

### Open only what the claim needs: commitments

A white-box claim need not reveal the model, nor make the kernel read all of it. The model is
**committed** (its hash is published, as a pool is), and the certificate opens only the parts the
check reads:

| Claim | What the check reads | What can stay hidden |
| --- | --- | --- |
| tree robustness on a small box | the reachable path of each tree (about `depth` nodes) | every subtree the box cannot reach |
| linear robustness, most features fixed | the weights of the varying features, and the fixed part of the score | the other weights, if their contribution is proved |
| exact MLP output on one input | each layer's intermediate activations, the weights they meet | nothing yet: every weight is used |

The rule that makes this sound is proved once per family: the check never reads a hidden part
(for trees, a hidden subtree must be unreachable from the box), so the claim holds for every model
that agrees with the opened parts, in particular the committed one. That the opened parts are the
committed ones is a Merkle inclusion check (A12). This reduces the request to the reached part,
and hides the rest of the model. Proving that a hidden contribution is correct without opening it
(the fixed part of a linear score) needs a zero-knowledge proof: that is the place where succinct
proofs come in, later ([architecture/system.md](architecture/system.md)).

## 3. The recipe, for every claim type

| Step | What | Proof obligation |
| --- | --- | --- |
| 1. Reference check | a plain Lean function on integers, in `Checks/` (core Lean) | `*_sound`: an accepted check implies the claim, then the claim type's `Sound` |
| 2. Kernel form | recursors, direct primitives, literals | `*K_eq`: equal to the reference |
| 3. Packed form | whole vectors in big integers, with the intermediate quantities as literals | `*_packed_eq` (or `*_of_packed`): an accepted packed check implies the reference check |
| 4. Both lanes | the compiled lane runs the same function on the same Lean decoder's output | `run*_eq`; `ot_kernel --compare` in CI |
| 5. Measured | a row in `docs/benchmarks.md`, run in CI | none |

Steps 2 and 3 change only the speed: the guarantee, the claim type and the level are those of step 1.

## 4. Where each check stands

| Check | Reference + proof | Kernel form | Packed form | Kernel time today | Target |
| --- | --- | --- | --- | --- | --- |
| `linear-monotone` | ✓ | ✓ | not needed | 0.13–0.26 ms | ✓ |
| `linear-robust` | ✓ | ✓ | ✓ `linear-robust-packed` (`Specs/LinearPacked.lean`): weights as `W⁺ − W⁻`, bounds shifted by `O` and reversed, the least score `W⁺·L − W⁻·H` by two products, digit sums by one remainder each | per feature: 0.8 ms (10), 11 ms (200); packed: 0.25 ms (10), 0.5 ms (200), 0.8 ms (1,000) | ✓ under a millisecond to 1,000 features |
| `mlp-exact` (exact MLP output) | ✓ (`Specs/MLPExact.lean`) | ✓ | ✓ | 0.4 ms (1,210 params), 2 ms (101,770) | ✓ under a millisecond for small networks, `verified` |
| `pool-sample` (beacon sample) | ✓ | ✓ | planned: blocks, quotients and indices packed; `B = Q·N + J` in one product, `J < N` by guard bits; outcomes by one `xor` and a zero test per slot | 28 ms (1,000 items), 1.2 s (20,000) | < 1 ms |
| `pool-witness` (Chernoff tail) | ✓ | ✓ | planned: witness powers rounded upwards to a fixed precision | 9 ms (1,000), 0.48 s (20,000) | < 1 ms |
| `tree-robust` | ✓ | ✓ | planned: trees padded to complete depth `D` in heap order; every node's box bound gathered by one product; reachability level by level by shifts and masks; leaves against bounds by guard bits; and opened paths only | 4 ms (10 trees), 0.16 s (500) | < 1 ms |
| `tree-monotone` | ✓ | ✓ | as above, cuts against leaves by guard bits | 17 ms (10), 1.4 s (500) | a few ms |

Measured, then discarded: a one-pass monotonicity check that carries the cuts down the tree was
20% slower than re-scanning subtrees; a tree node costs about 40 µs whatever the algorithm around
it, so only packing removes that cost.

## 5. Why this route, among the fast certificates others use

| Approach | Check time | What it adds to the trust | Why not, or when |
| --- | --- | --- | --- |
| a signature over the result | ~50 µs | the signer | it attests who checked, not that the claim holds |
| a verified compiled checker (`cake_lpr` for SAT proofs [@tan2021cakelpr]) | µs | a verified compiler, in another logic (HOL4) | only if a user requires machine-code verification |
| a succinct proof (a SNARK or a zkVM running `ot_check`) | ~1 ms whatever the size | the proof system's cryptography and the circuit | later, to show a result **without** revealing the model or the data |
| **a packed kernel check** | ~0.1–1 ms | nothing: the Lean kernel and GMP | the main route |

The packed kernel check is the arithmetization a SNARK would use, checked directly by the kernel
with big integers instead of by cryptography: nothing is added to what a `verified` result trusts.

## 6. Next, in order

1. **`mlp-exact` proved (done).** The packed MLP check, 0.4–2 ms, is proved against
   `Exact.reluMLP` (`Specs/MLPExact.lean`): the first sub-millisecond white-box check that is
   `verified`. Its slot lemmas (`Foundations/Arithmetic/Slots.lean`) and layer relations are the
   template for the next packed checks and for every network check (robust accuracy, intervals per layer).
2. **Packed `linear-robust` (done).** Two Kronecker products and two remainders modulo `2^B − 1`
   (`Checks.Linear.robustPackedN`, `Specs/LinearPacked.lean`). It fixed the pattern: signed values as
   a positive and a negative part, or shifted by an offset `O`; slot widths `B` with
   `d · 2^(mW + mL) < 2^B − 1`, checked by the kernel with `digitsBelow`; one lemma per relation
   (`dotSlot_eq`: the middle digit of a product is the dot product). The theorem speaks of the model
   and box the request stores (`packedModel`, `packedBox`), and the conformance test unpacks them.
   The time left is mostly reading the request's decimal numbers.
3. **Packed `pool-sample` and Chernoff tails**, so that every black-box rate checks in under a
   millisecond.
4. **Packed and opened trees**: complete trees in heap order, opened paths, hidden subtrees under
   the commitment.

Each step ends with its row in [benchmarks.md](benchmarks.md) under a millisecond, and with the
same guarantee as before.
