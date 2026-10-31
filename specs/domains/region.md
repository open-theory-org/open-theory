+++
id = "region"
kind = "region"
randomness = "none"
assumptions = []
lean = ["OpenTheory.Domain", "OpenTheory.sound_exact_iff"]
references = [{ key = "gowal2018ibp", relation = "background" }]
+++
# Domain: region

Every input of a set: a box around an input, an ℓ∞ ball, a finite list
of inputs. With the aggregate `all`, there is no randomness: a certificate is checked exactly and
`δ = 0`, so an accepted claim is true (`sound_exact_iff`).
