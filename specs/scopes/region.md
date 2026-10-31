+++
id = "region"
kind = "region"
randomness = "none"
assumptions = []
lean = ["OpenTheory.Scope", "OpenTheory.sound_exact_iff"]
references = [{ key = "gowal2018ibp", relation = "background" }]
+++
# Scope: region

The property must hold on every input of a set: a box around an input, an ℓ∞ ball, a finite list
of inputs. There is no randomness: a certificate is checked exactly and `δ = 0`, so an accepted
claim is true (`sound_exact_iff`).
