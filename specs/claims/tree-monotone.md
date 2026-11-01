+++
id = "tree-monotone"
observable = "monotone"
domain = "region"
aggregate = "all"
models = ["tree-ensemble"]
lean = ["OpenTheory.Checks.Tree.monotoneCert", "OpenTheory.Checks.Tree.monotoneCertK", "OpenTheory.Checks.Tree.monotoneCert_sound"]
claim_types = ["OpenTheory.ClaimTypes.treeMonotone"]
assumptions = ["A3-model-binding", "A11-tree-translation"]
references = [{ key = "devos2021versatile", relation = "implements" }]
+++
# Claim: monotonicity of a tree ensemble in one feature (`tree-monotone`)

**Statement.** On the box `B`, raising feature `j` (all other features fixed) never lowers the
ensemble's score (or, decreasing, never raises it). With an unbounded box it is global.

**Spec.** Observable: the property on pairs "raising `j` moves the score in the stated direction".
Domain: the region of pairs `{(x, x') | B.Mem x ∧ B.Mem x'}`. Aggregate: `all`.
`OpenTheory.treeMonotone_sound` proves `Sound` with `δ = 0`.

**Check.** `Checks.Tree.monotoneCertK` (equal to `monotoneCert`). Every tree is monotone, which
suffices for a sum [@devos2021versatile]. At every reachable split on `j` the certificate gives a
cut; the kernel checks that every leaf reachable below the threshold is at most the cut and every
leaf reachable above it at least (reversed if decreasing), recursively. Sound
(`monotoneCert_sound`); incomplete (a sum can be monotone without each tree being so).

**Does not cover.** Features other than `j`; preprocessing; A3, A11.
