+++
id = "distribution"
kind = "distribution"
randomness = "iid"
assumptions = ["A1-iid"]
lean = ["OpenTheory.Domain", "OpenTheory.BinomialTail.clopperPearson"]
references = [{ key = "clopper1934use", relation = "implements" }]
+++
# Domain: distribution

The distribution `D` the examples were drawn from, known only through assumption A1. The evidence is `n` IID draws; the guarantee holds for every `D`, uniformly in the count and
the bound the certifier picks after seeing the sample (Clopper–Pearson).
