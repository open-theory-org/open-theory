+++
id = "population-iid"
kind = "population"
randomness = "iid"
assumptions = ["A1-iid"]
lean = ["OpenTheory.Scope", "OpenTheory.BinomialTail.clopperPearson"]
references = [{ key = "clopper1934use", relation = "implements" }]
+++
# Scope: population, IID sample

The property must hold on all but a fraction `p` of the distribution `D` the examples were drawn
from. The evidence is `n` IID draws; the guarantee holds for every `D`, uniformly in the count and
the bound the certifier picks after seeing the sample (Clopper–Pearson).
