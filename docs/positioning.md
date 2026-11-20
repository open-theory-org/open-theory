# What OpenTheory adds

This page compares OpenTheory with prior work. It covers what already exists, what OpenTheory adds
today, what it aims to add, and how its goal and impact differ. It was compiled on 2026-10-31 and
2026-11-02 from abstracts and summaries, not full papers. Sources are in
`blueprint/src/references.bib`. More detail on tabular models is in
[research/literature/verifiable-traditional-ml.md](../research/literature/verifiable-traditional-ml.md),
and on private verification in [privacy.md](privacy.md).

Running example: a bank must show a regulator three facts about its credit model (gradient-boosted
trees) without handing over the model.

| # | Fact |
| --- | --- |
| 1 | at most 3% of this month's applicants are wrongly declined, with 95% confidence |
| 2 | Alice's decision is the same for every income within ±5% of hers |
| 3 | the approval rates of two groups differ by at most 5 points |

## 1. In one sentence

Prior work asks *is this claim true?* and answers it for whoever runs the tool. OpenTheory asks
*can someone who trusts nobody check that it is true?* To make that possible, it turns every claim
about a model into a certificate that carries its proof, its confidence and its assumptions.

## 2. Is it necessary, and does it matter?

### When it is necessary

A certificate that anyone can check is needed only when the reader cannot simply trust the
producer. Three conditions make that the case:

| Condition | Bank → regulator | AI lab → public | Model vendor → bank |
| --- | --- | --- | --- |
| The producer gains from a favourable result | yes | yes | yes |
| The reader cannot see the model or the data | partly (a supervisor can inspect, at a cost) | yes | yes |
| The claim must be repeated (each month, model, group) | yes | yes | yes |

Where all three hold, today's alternatives fail in known ways:

- an audit set chosen after the model can be gamed: one model was certified at over 99% accuracy
  and scored under 30% on fresh data [@luck2026certified];
- the solver-based robustness tools for tree ensembles have had bugs;
- point estimates without confidence hide small samples and choices of subgroup;
- a validation report must be trusted as a whole, and is redone by hand for each model.

The three conditions also hold *inside* a large organisation (§2, "For the business itself").
They fail only for a small team that builds, checks and uses its own model. There, careful
statistics already do the job, and OpenTheory is a convenience.

### Which parts are necessary

| Part | Necessary? | Why |
| --- | --- | --- |
| Commit first, then sample from a public beacon | **yes**, whenever the producer has an interest in the result | it closes the known attack; without it a certified rate means little |
| Stated assumptions, confidence and non-claims | **yes** | the reader must know what was claimed and what was not |
| One meaning per claim type (a Lean statement) | important | the same claim means the same thing for every model and vendor, so claims compare and compose |
| Checking by the kernel | important when the reader trusts nobody; marginal when a trusted validator re-runs everything | most of the remaining risk is in the assumptions (binding, data, labels), which no kernel checks |
| Checks in milliseconds | **yes** at scale (per applicant, per month, per group) | otherwise certificates are made only for showcases |
| Privacy (enclave, zero knowledge) | **yes** for vendors and labs; not built | otherwise the reader must see the model |

The protocol and the claim format carry most of the value. The proof assistant makes them
trustless, uniform and cheap to extend: it fixes what each claim means, and it removes the
checker's code from what must be trusted. Catching arithmetic errors matters much less.

### For the business itself

A business needs to trust its own AI before anyone else does, and the three conditions recur
inside it. The developers gain from a model that ships. The validators and the internal auditors
do not rebuild the model, and for bought AI nobody inside sees the model. The checks repeat every
month. In the running example:

| Internal use | Today | With OpenTheory | The part that matters |
| --- | --- | --- | --- |
| **Release gate**: ship the model only if it is good enough | a score on a test set that has been reused many times, so the model is tuned to it, often without anyone intending it | the claim on a fresh sample drawn after the model is committed; ship if it holds | commit, then sample; confidence |
| **Monitoring**: is the model still good this month? | dashboards without confidence | one certificate per window; an alarm is a claim that failed, with a known false-alarm rate δ | checks in milliseconds; confidence |
| **Lines of defence**: developers, validation, internal audit | validation redoes the work by hand; audit trusts both | validation and audit re-run `ot verify` on the developers' certificates | the format; the kernel |
| **AI the business buys** (vendor scores, LLM APIs) | trust in the vendor's numbers | rates measured on the business's own committed logs, with no access to the model (`pool-rate`, `judged-rate`) | black-box claim types |
| **One customer's decision** (Alice complains) | an explanation (SHAP and the like) | a proof that her decision is the same on her box and never falls with income | white-box checks |
| **Decisions built on the model** (thresholds, provisions, risk appetite) | point estimates | bounds with confidence feed the decision | the statistics |
| **AI agents acting for the business** | logs reviewed afterwards | a gate that blocks actions outside policy (planned) | runtime checks |

The strongest internal argument is that **the work is done once**: the certificate that opens the
release gate is the one the auditor re-runs and the regulator receives. Today these are three
separate pieces of work.

Inside the business, the kernel matters less than the protocol and the statistics, because the
reader can usually trust the checker. OpenTheory also does not tell the business whether the
model serves its objective, or how it will behave under a future shift. It certifies the stated
claims, on the stated data.

### Whether it matters

- **Now, in finance: modest but real.** Supervisors ask for independent validation (SS1/23
  [@pra2023ss1]) and for accuracy and robustness (EU AI Act Article 15 [@euaiact2024]); neither
  asks for proofs. The value is validation that is cheaper, can be repeated, and survives an
  adversarial reading. Externally, it matters only if a validator or supervisor accepts a
  certificate in place of part of their current work, which has not been tested. Internally, it
  needs no one's permission: a release gate, monthly monitoring and checks on bought AI are useful
  on their own, and they are the natural first use.
- **Later, for AI in general: potentially large.** As AI systems make decisions at scale and their
  makers publish claims about safety, the gap grows between the claims that are made and the
  claims anyone can check. Evaluations, model cards and safety cases rest today on trust in the
  maker. An open, shared way to check such claims, with their assumptions stated, does not exist,
  and such infrastructure is hard to add late: Certificate Transparency came after the
  certificate authorities had failed [@laurie2021rfc9162].
- **What would make it unimportant:** readers never demanding to check (trust in auditors
  suffices); the claims that matter not being expressible as checkable claims (OpenTheory covers
  rates and properties on regions, not open-ended "safety"); or another standard winning, such as
  zero-knowledge ML alone or a testing lab run by a regulator.

**The test.** Put the certified credit report in front of one model owner, one model validator and
one supervisor, and ask each which part of their current work it replaces. If the answer is "none", the product is
wrong, even if the mathematics is right.

## 3. The three facts, today and with OpenTheory

| Fact | How it is established today | What the regulator must trust | With OpenTheory |
| --- | --- | --- | --- |
| 1 | the validation team measures the error on a test set, perhaps with a confidence interval | the team, its code, and a test set chosen after the model, which can be gamed [@luck2026certified] | `pool-rate`: the model is committed first; the Lean kernel derives the sample from a public beacon drawn afterwards, counts the failures and checks the binomial tail |
| 2 | a solver (MILP, veritas, silva) or a sensitivity sweep | the solver's code (a comparative study found bugs in silva and VoTE) and its floating point | `robust-decision`: the kernel checks the trees on the box against a theorem proved once, in exact arithmetic |
| 3 | a fairness report with point estimates | the report's data and code | `rate-gap`: two committed pools, one beacon, one guarantee for the gap |
| all | a validation document reviewed by people (independent validation, SS1/23 [@pra2023ss1]) | the validator's reputation | anyone runs `ot verify` offline; what remains to trust is listed by name (A3: the certified model is the deployed one; A11: the LightGBM translation; A10: group membership) |

## 4. Prior work, strand by strand

| Strand | Closest work | What it gives | What it leaves open | What OpenTheory takes or adds |
| --- | --- | --- | --- | --- |
| Evaluation harnesses | HELM [@liang2022helm], Inspect [@inspectai] | reproducible scores on benchmarks | a number, with no confidence and no sampling protocol; you trust the harness | uses harnesses as untrusted producers, and turns their per-example bits into rate claims (`pool-rate`, `judged-rate`) |
| Statistics in a proof assistant | MLCert [@bagnall2019certifying] | Coq-checked bounds on true error, from test or training error, for quantized networks | an IID test set is assumed; no commit-then-sample; no rates on production pools; no group gaps | the same idea (`heldout-error`, `occam-code-error`, `pacbayes-error`), plus design-based rates: the kernel derives the sample, so the pool needs no IID assumption |
| Statistical certificates elsewhere | randomized smoothing [@cohen2019certified]; prediction-powered inference [@angelopoulos2023prediction] | probabilistic certificates per input; valid inference with an AI judge | computed, and believed, in Python | `judged-rate`: a judge plus a small gold audit, finite-sample, checked in the kernel |
| Gaming of certification | Luck et al. [@luck2026certified] | nine cryptographic certification schemes can be gamed; the fix is to commit first, then sample | the fix is in Python, and its theorem is not machine-checked | the fix in the kernel: the beacon-derived sample (`pool-sample-packed`, 0.3 ms for 1,000 items) |
| Neural-network verifiers | Reluplex/Marabou [@katz2017reluplex], β-CROWN [@wang2021beta], IBP [@gowal2018ibp] | robustness of one input, at scale | you trust the solver's code and its floating point | solvers become untrusted producers, and the kernel checks their witnesses (for networks the theorem exists; the method is not built yet) |
| Proof production, verified checkers | Marabou proofs [@isac2022proof], a certified checker for them [@desmartin2024checker], `cake_lpr` [@tan2021cakelpr], proof-carrying code [@necula1997proof] | the pattern: untrusted search, small trusted checker | built per solver and per property | the same pattern, as the rule for every claim type |
| ML in Lean | TorchLean [@torchlean], LeanCert [@leancert] | network semantics, interval and CROWN-style certificate checking, certified numerics | per-input robustness of networks; no statistics, no tabular models, no certificate format for third parties | builds on TorchLean; adds model families, statistics, a format and a verifier |
| Specification languages | Vehicle [@daggitt2022vehicle] | one specification, compiled to verifier queries and to Agda | the network is a black box in the prover; robustness-style properties only; you trust the verifier | one `Spec` (observable × domain × aggregate) for rates, gaps, robustness and monotonicity, with one guarantee, `Sound` |
| Tree ensembles | [@kantchelian2016evasion; @chen2019robustness; @devos2021versatile; @ranzato2020abstract; @tornblom2019formal; @calzavara2025boosted] | exact or bounded robustness; monotonicity | trusted solvers, with bugs found; nothing found in a proof assistant | `tree-ensemble-check`, verified: robustness in 4 ms (10 trees) to 0.19 s (500 trees) |
| Fairness verification | FairSquare, VeriFair, Justicia [@albarghouthi2017fairsquare; @bastani2019verifair; @ghosh2021justicia] | distributional fairness of trees and logistic regression | solvers; the input distribution is assumed; nothing found for ensembles | `rate-gap`, `rate-ratio`: design-based, on committed pools, for any system |
| Zero knowledge | zkDT, Kang et al., ZKBoost, Terrae, FairProof, ZK-SR117 [@zhang2020zkdt; @kang2022scaling; @melissaris2026zkboost; @gao2026terrae; @yadav2024fairproof; @uddin2026zksr117] | proof that a computation (inference, training, a metric) was done, without revealing the model | what the computation means: accuracy on a dataset rather than a population bound, and a sample the prover chooses ([privacy.md](privacy.md) §2) | integrated, not built: the kernel in an enclave, or a proved count with the bound checked in the clear |
| Proofs from interpretability | compact proofs [@gross2024compact] | proved accuracy lower bounds for small transformers, derived from understanding them | toy tasks, one proof per model | planned: certified rates of circuit faithfulness; ablation bounds (library theorems today) |
| Frameworks and programmes | Guaranteed Safe AI [@dalrymple2024guaranteed], ARIA Safeguarded AI [@aria2025safeguarded], Verified AI [@seshia2022toward], safety cases [@clymer2024safety] | the vision: world model, specification and verifier; structured arguments for safety | top-down and mostly aimed at future systems; the leaves of a safety case are evidence someone must believe | bottom-up: checkable claims about models deployed now, each usable as a checkable leaf of a safety case |

## 5. What OpenTheory adds today

1. **One guarantee for every claim.** `Sound` says that the probability of accepting a false claim is at most `δ`
   ([language.md](language.md)). Proofs have `δ = 0` and statistics have `δ > 0`. Elsewhere,
   verifiers and statisticians use separate tools, so a report that mixes them has no single
   meaning. Here a report is `Sound.and`, and its `δ`s add.
2. **A language, not a tool.** A claim is an observable × a domain × an aggregate, stated against
   model interfaces. A property stated once holds for every family that implements the interface,
   so adding a family, property or aggregate costs one definition and one proof. Today: ten
   claim types; trees, linear and logistic models, ReLU networks and quantized MLPs on the white-box
   side; any system on the black-box side.
3. **Checkable by a third party.** A certificate and `ot verify` are all a reader needs. The kernel
   re-checks every certificate, and the producer is untrusted and may be closed. Conformance tests
   reject forgeries: a false count, an overclaim, tampered data, a tampered model.
4. **A sample nobody chose.** The beacon is drawn after the commitment and the kernel derives the
   sample from it, so black-box rates need no assumption about how the data were drawn.
5. **The models banks run.** Tree ensembles and logistic regression are proved in Lean. We found
   no other proof-assistant treatment of tree ensembles.
6. **Proved once, checked in milliseconds.** In the kernel: a 100k-parameter MLP in 2.2 ms, linear
   robustness with 1,000 features in 0.7 ms, a beacon sample of 5,000 items in 0.7 ms
   ([benchmarks.md](benchmarks.md), [fast-certificates.md](fast-certificates.md)).
7. **Honest labels, enforced.** Every result carries a level, a lane and its assumptions
   ([trust.md](trust.md)). Levels are derived by CI, not declared. Of 13 methods, 11 are
   `verified`, 1 is `specified` and 1 is `experimental`.

## 6. What it aims to add: the vision

The research question is *how can we derive independently checkable behavioural guarantees
about learned systems from incomplete information about them?* ([PLAN.md](PLAN.md) §1). It
splits into four questions, each owned by a different discipline. OpenTheory's aim is the shared
foundation that connects them.

| Question | Discipline | What OpenTheory provides | Status |
| --- | --- | --- | --- |
| What can we know about an AI system? | deep-learning theory, interpretability | observables on weights and internals; library theorems (generalization, ablation, plateau) | library theorems; access to internals not built |
| What guarantees follow from that knowledge? | mathematical and statistical verification | claim types with a `Sound` theorem | ten claim types |
| How can anyone check them? | formal proofs, cryptography, evidence protocols | kernel, beacon, Merkle commitments, timestamps; enclave or zero knowledge for privacy | built, except privacy |
| What makes them worth having? | alignment, safety, decision theory | claims about what people care about: fairness, robustness, policy compliance, refusal | fairness and robustness built; agents planned |

The idea that makes the vision buildable is that **any per-example yes/no check becomes a
population guarantee.** This includes checks that need the weights, such as robustness on a box,
a circuit agreeing with the model, a monitor firing, or an agent staying within its policy. The
claim then climbs a ladder:

| Level | Form | Today → planned |
| --- | --- | --- |
| L0 evidence | "we measured X" | where most interpretability and evaluation results sit |
| L1 statistical | "with confidence 1−δ, the rate is ≤ p in the population" | built (black box) → circuit faithfulness, monitors, LLM behaviour rates |
| L2 local universal | "for every input in this region, P holds" | built (trees, linear) → networks |
| L1 ∘ L2 | "with confidence 1−δ, ≥ 1−p of the population is certified robust" | planned next (`robust-accuracy`) |
| L3 global | "for every input, P holds" | monotonicity built → Lipschitz bounds, ablation bounds |

It also climbs in access: black box → white box → internals → runtime (the agent policy gate) →
private (the same certificates, checked without seeing the model).

**How the vision differs from Guaranteed Safe AI and ARIA.** They aim at proofs about an AI's
effects in the world, which need formal world models that do not exist for most domains. ARIA
moved in November 2025 from dedicated ML teams towards a formal-verification toolkit
[@aria2025safeguarded]. OpenTheory starts from claims that can be checked now, on deployed
models. It mixes statistics with proofs, names the trust boundary (the assumptions), and raises
the level claim by claim. The two approaches are complementary: a verifier in the Guaranteed Safe
AI style could emit OpenTheory certificates.

## 7. How the project, the goal and the impact differ

| | Typical prior work | OpenTheory |
| --- | --- | --- |
| **Question** | Is P true of this model? Can P be computed faster? | Can a third party check P without trusting the producer? |
| **Output** | a score, a solver's verdict, a paper, a proof about one model | a certificate: claim, evidence, level, lane, assumptions |
| **Trusted** | the tool, the evaluator, the auditor, floating point | the Lean kernel and the named assumptions |
| **Scope** | one property, one model class, one community | one language for proofs and statistics, across model families and access levels |
| **Unit of progress** | a better algorithm | a claim type proved once, usable for every model of the family |
| **Openness** | a closed product or a research prototype | open format, theorems and verifier; producers may stay closed (Structure and Soul): open checking, closed production |
| **For whom** | the model owner | the reader of the claim: regulator, auditor, counterparty, public |

**Impact.** The aim is three shifts:

1. **From trusting the validator to checking the certificate.** Independent validation becomes a
   re-check anyone can run, and costs nothing to repeat for each model, month or group.
2. **Claims become comparable and composable.** The same claim type means the same Lean statement
   whichever vendor, model or bank produced it, and reports are built by composing claims.
3. **Honesty becomes enforceable.** Levels are derived, not declared. The non-claims are stated.
   The known way to game a certification (choosing the audit data) is closed by the protocol.

In the longer term, the aim is for claims about AI systems to move from reputation to public,
mechanical checks, as Certificate Transparency did for web certificates [@laurie2021rfc9162].

## 8. What is not new, and the limits

- **The techniques are known:** binomial and Chernoff tails, interval bound propagation, tree
  robustness algorithms, proof by reflection, Kronecker substitution [@harvey2009kronecker],
  commit-then-sample [@luck2026certified]. What is new is the combination: kernel-checked, for
  production model families, under one guarantee, in a format a third party can check.
- **Assumptions remain.** The kernel cannot check the world. A3 (binding to the deployed model),
  A11 (the translation from LightGBM) and A10 (group membership) are stated, not proved.
- **Scale.** The kernel checks white-box claims on small models (100k-parameter MLPs, 500 trees).
  Large language models are reached only through rates over a harness's outputs.
- **Not built yet:** calibration and AUC, `robust-accuracy`, the privacy route, the agent gate,
  access to internals, the end-to-end credit report.
- **The field is moving.** JPMorgan researchers co-authored both the analysis of gaming and ZKBoost
  [@luck2026certified; @melissaris2026zkboost]. ZK-SR117 targets US model-risk guidance directly
  [@uddin2026zksr117]. None of these, as far as we found, proves what a certified number means
  in a proof assistant; that is the part OpenTheory adds.
- **This comparison is from abstracts.** The next check is a full reading of MLCert, Vehicle,
  LeanCert and TorchLean.
