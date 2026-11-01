+++
id = "pacbayes-error"
observable = "wrong"
domain = "distribution"
aggregate = "meanLe"
models = ["quantized-mlp"]
lean = ["OpenTheory.PACBayes.catoni_pacBayes"]
claim_types = ["OpenTheory.ClaimTypes.pacBayes"]
assumptions = ["A1-iid", "A2-heldout-independent", "A4-labels"]
references = [{ key = "catoni2007pac", relation = "implements" }]
+++
# Claim: PAC-Bayes error bound (`pacbayes-error`)

**Statement.** Catoni's bound for a posterior over a finite code space, with a prior learned on
separate data.

**Spec.** Observable: the property "the code errs on `z`". Domain: the data distribution.
Aggregate: `meanLe B`. `OpenTheory.pacBayes_sound` proves `Sound` for this `Spec.Target` with the
stated `δ`, over `n` IID observations independent of the reference code `c` (A2), uniformly over `B`
and the witnesses `t, q, γ, c', E, L` of Catoni's inequality and its rational inversion. The
empirical error `q` is the kernel's error count (`quantized-mlp-kernel-inference`).

**Does not cover.** A prior that saw the bound sample (A2); posteriors other than the Dirac at `c`
in the shipped certificate; mislabelled data (A4).
