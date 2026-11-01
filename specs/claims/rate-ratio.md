+++
id = "rate-ratio"
observable = "event"
domain = ["pool", "pool"]
aggregate = "ratioGe"
models = ["any-system"]
lean = ["OpenTheory.RateGap.Claim", "OpenTheory.RateGap.target_ratio", "OpenTheory.PoolRate.Claim.of_poolCheck"]
claim_types = ["OpenTheory.ClaimTypes.rateRatio"]
assumptions = ["A5-beacon", "A6-timestamp", "A7-issuer-identity", "A10-group-membership"]
references = [{ key = "clopper1934use", relation = "implements" }, { key = "luck2026certified", relation = "background" }]
+++
# Claim: Rate ratio between two committed pools (`rate-ratio`, v0.1)

**Statement.** An issuer commits to two pools, `A` and `B` (for example the scored credit
applications of two groups), and to a counted output (for example `"approve"`). One drand round
published after the commitment samples both: blocks `0 … nA−1` of the expanded seed select items of
`A`, blocks `nA … nA+nB−1` items of `B`. On each sample, upper bounds on the rate of the output and
of its complement give an interval `[1 − q, p]` for each pool's rate. The claim is
c · rB ≤ rA (the four-fifths rule is c = 4/5; pool A is the protected group),
wrong with probability at most `(1 + NA/2²⁵⁶)^nA (δA + δA') + (1 + NB/2²⁵⁶)^nB (δB + δB')` over the
round, uniformly over the counts and bounds chosen after seeing the sample.

**Spec.** Observable: the property "the output is the counted one". Domain: the pair of committed
pools (`RateGap.pools`, items of `A` and `B` as `Fin NA ⊕ Fin NB`). Aggregate: `ratioGe`.
`OpenTheory.RateGap.ratio_sound` proves `Sound` for exactly this `Spec.Target`; each pool's blocks are
uniform by `DesignSampling.seedFrac_restrict`.

**Protocol.** As [`pool-rate`](pool-rate.md), with procedure kind `two-pool-match`
(`positive`: the counted output), `pool_b`, `sample.n_b` and four committed δ. `sample.json` has
`items` (pool A) and `items_b` (pool B). The claim has parts `upperA`, `lowerA`, `upperB`,
`lowerB`, each `{count, bound, witness?}`, and `c`, with `c · pB ≤ 1 − qA` required.

**Verifier checks.** The `pool-rate` steps for both pools, the four bit vectors through
`Checks.poolCheck` in the kernel (`ot_kernel`; `--compiled` is labelled not verified), and the
aggregate's inequality on the four bounds.

**Assumptions.** `A5-beacon`, `A6-timestamp`, `A7-issuer-identity`, `A10-group-membership`.

**Does not cover.** Applications outside the committed pools; whether the pools are the right
groups (`A10`) or the rate the right metric; why the rates differ.

**Example.** [`examples/rate_gap/`](../../examples/rate_gap/): 5,000 decisions per group certify
gap ≤ 9.67% and ratio ≥ 0.846 at δ = 10⁻³.
