+++
id = "population-pool"
kind = "population"
randomness = "pool-seed"
assumptions = ["A5-beacon", "A6-timestamp", "A7-issuer-identity"]
lean = ["OpenTheory.Scope", "OpenTheory.seedLaw", "OpenTheory.DesignSampling.rate_sound"]
references = [{ key = "luck2026certified", relation = "background" }]
+++
# Scope: population, committed pool

The property must hold on all but a fraction `p` of a committed pool of `N` items. A public beacon
seed published after the commitments selects the sample, so nothing is assumed about how the pool
arose: the randomness is the seed's. The bound carries the factor `(1 + N/2^b)ⁿ` of reducing seeds
modulo `N`. Committing before sampling is what defeats a gamed audit set.
