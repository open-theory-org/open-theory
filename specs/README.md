# specs/: what a claim means and how it is checked

| Folder | Contents |
| --- | --- |
| [claims/](claims/) | Types of verifiable claims and their Lean statements |
| [properties/](properties/) | Properties a claim can be about: accuracy, robustness, causal, safety |
| [assumptions/](assumptions/) | Every assumption a certificate may rely on, by id |
| [evidence/](evidence/) | What evidence each claim needs and who may produce it |
| [certificates/](certificates/) | Certificate formats |
| [protocols/](protocols/) | [Assurance levels](protocols/assurance-levels.md) and [verification steps](protocols/verification.md) |

Specs are versioned. A claim type is only `verified` once its Lean statement exists in `formal/`.




Types of assurances 

Assurance type	Meaning
Formal	A mathematical proposition has a valid machine-checked proof
Deterministic	A specified system property has been established for a stated scope
Statistical	A probabilistic guarantee follows under documented assumptions
Empirical	An observed result is supported by reproducible evaluation evidence
Cryptographic	A defined computation or relation is proven without exposing specified private information
Runtime	An enforcement mechanism has checked or enforced a specific operational constraint