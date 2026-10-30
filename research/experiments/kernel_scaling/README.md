# Kernel scaling probe: can the checked MLP certificate reach MNIST size?

Measured 2026-10-24 on one 10-core, 16 GB laptop (other applications open).
Generators: `research/experiments/kernel_scaling/`. Weights and pixels are random: kernel cost
depends on the number of integer operations, not on their values. Each
error-count theorem was checked against the Python mirror of the decoder,
so a wrong count would fail.

## Results

Same decoder as the certificates (`OpenTheory.QuantizedMLP.scoresOfWeights`)
and the same proof (`rw [errorCount_codeOfList]; decide +kernel`). Times are
Lean's profiler output for kernel type checking.

| Network | Params | Weight storage | Decode + length check | Error check, 1 row | 5 rows | Peak memory |
| --- | --- | --- | --- | --- | --- | --- |
| 784–4–10 | 3,190 | packed | 0.26 s | 1.2 s | 2.5 s | 1.9 GB |
| 784–16–10 | 12,730 | packed | 1.0 s | 5.5 s | 16 s | 3.6 GB |
| 784–64–10 | 50,890 | packed | 4.7 s | 71 s | stopped after 15 min (swapping) | 5.4 GB at 1 row |
| 784–256–10 | 203,530 | list literal (current exporter) | elaboration fails: max recursion depth after 265 s, 4.2 GB | — | — | — |
| 784–256–10 | 203,530 | packed | 842 s (swapping) | stopped after ~10 h wall, < 9 min CPU | — | ≥ 6 GB |

"Packed" stores the 2-bit codes as base-4 digits of 204 large naturals and
each image as one base-256 natural, both decoded by the kernel. This fixes
elaboration (0.18 s) but not kernel evaluation.

**Kronecker substitution (micro-probe).** Pack each hidden unit's 784 codes
and the reversed image into naturals with 20-bit slots (3·255·784 < 2²⁰, so
there are no carries). Slot 783 of their product is the dot product. For the
784–256–10 network, all 256 hidden-unit dot products of one image, 200,704
multiply-adds and 98.6% of the forward pass, check by `decide +kernel` in
**0.1 s** (plus 2.4 s to parse the literals once per file, 1.3 GB). Changing
one expected value by 1 makes the check fail, as it should.

## What this means

1. **The current exporter cannot produce an MNIST-sized certificate.** A plain
   list literal of 2×10⁵ weights does not elaborate.
2. **The list decoder is superlinear in kernel time and memory.** Marginal
   cost per row is about 0.33 s at 3.2k parameters and 2.6 s at 12.7k, i.e.
   100 → 200 µs per multiply-add, with memory growing alongside. It is
   practical up to about 10⁴ parameters: 784–16–10 on the 10,000 MNIST test
   rows would take about 7 CPU-hours, with only 3–4 processes in parallel on
   16 GB.
3. **Kronecker packing removes the bottleneck.** The large products are GMP
   multiplications that the kernel performs natively. A full 784–256–10
   forward pass costs on the order of 0.1 s per image, so 10,000 images take
   roughly 20 minutes. The trusted base is unchanged: no `native_decide`, no
   new axioms.

## Proved packed inference (done)

`formal/core/Foundations/Arithmetic/Kronecker.lean` proves the substitution
(`kronecker_dot`), slot decoding (`pack_slots`) and slot bounds from one
bitwise `and` (`slot_lt_of_land_eq_zero`).
`formal/core/Models/QuantizedMLP/Packed.lean` defines the packed forward
pass and proves it equal to the reference decoder (`scoresPacked_eq`), so
error counts transfer (`errorCount_packed`). The side conditions are a
length, one comparison and one `and` per packed number.

End to end on the 784–256–10 probe network (203,530 parameters), via
`research/experiments/kernel_scaling/gen_packed_certificate.py`: the theorem
`errorCount arch (codeOfList _ (net.codes arch)) (packedObservations …) = e`,
with all side conditions by `decide +kernel`, axioms `propext`,
`Classical.choice`, `Quot.sound` only.

| Rows | Errors (= Python mirror) | Kernel, error-count theorem | Wall, whole file | Peak memory |
| --- | --- | --- | --- | --- |
| 1 | 1 | 0.74 s | 12 s | 1.6 GB |
| 20 | 18 | 5.9 s | 16 s | 2.7 GB |
| 1, count off by one | — | rejected | 11 s | 1.8 GB |

About 0.28 s per row, against no row at all in 10 hours with the list
decoder. The output layer is still evaluated as lists (2,560 weights) and is
the likely remaining per-row cost (not profiled); packing it the same way is
the obvious next speed-up.

## What a real certificate still needs

- An exporter that emits packed literals, with a Python mirror for `verify`.
- A trained network and data with recorded provenance.
- For a training-data-only bound, the Occam theorem over a prefix-free code
  (see `docs/mnist-occam-feasibility.md`).

For scale on the statistics side: with the exact binomial bound
(`OpenTheory.BinomialTail`) at 95% on 10,000 held-out rows, 1% / 2% / 3% /
5% observed error certify 1.18% / 2.25% / 3.30% / 5.37%.
