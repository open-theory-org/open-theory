# Verifiable traditional ML: landscape (2026-10-31)

Context: a bank wants to check the reliability and robustness of production models (credit, fraud, AML: mostly gradient-boosted trees, logistic regression, small MLPs) and show the result to regulators and auditors without revealing the model. Searched 2026-10-31 from abstracts and summaries, not full papers. Citations are keys of `blueprint/src/references.bib` (checked by `tests/regression/check_references.py`).

## What exists

| Strand | Work | What it gives | Gap for OpenTheory |
| --- | --- | --- | --- |
| Robustness of tree ensembles | MILP, NP-completeness [@kantchelian2016evasion]; max-clique, much faster [@chen2019robustness]; anytime bounds, several tasks [@devos2021versatile]; abstract interpretation (silva) [@ranzato2020abstract]; VoTE [@tornblom2019formal] | Exact or bounded robustness for random forests and GBDTs | Solvers to be trusted; a comparative study found bugs in both silva and VoTE |
| Verifiable by design | Large-spread ensembles: polynomial-time ℓ∞ verification, pseudo-polynomial for ℓp; LightGBM extension [@calzavara2023verifiable; @calzavara2025boosted] | Fast exact robustness for boosted trees trained the right way | A natural first algorithm for an exact check |
| Monotonicity | XGBoost/LightGBM monotone constraints (training); per-tree checks for additive ensembles (sufficient condition) [@devos2021versatile] | Exact, cheap | A natural first property |
| Fairness | FairSquare [@albarghouthi2017fairsquare], VeriFair [@bastani2019verifair], Justicia [@ghosh2021justicia] | Distributional fairness of trees and logistic regression | Solver-based; nothing found for ensembles |
| Zero knowledge | Tree predictions and accuracy [@zhang2020zkdt]; fair tree training [@shamsabadi2023profitt]; fair neural networks [@yadav2024fairproof]; audits on committed models and data [@waiwitlikhit2024zkaudit]; XGBoost training [@melissaris2026zkboost]; GBDT training and inference [@gao2026terrae] | Show a property without revealing the model | Building blocks to integrate, not rebuild |
| Small trusted checkers | Verified SAT proof checker in CakeML, used by the SAT Competition [@tan2021cakelpr]; certified checker for Marabou certificates [@desmartin2024checker] | The verified-checker pattern, for SAT and neural networks | Nothing found for tree ensembles in a proof assistant |
| Statistics and ML in a proof assistant | Verified generalization bounds in Coq (MLCert) [@bagnall2019certifying]; network semantics and certificate checking in Lean [@torchlean; @leancert]; a specification language compiled to Agda [@daggitt2022vehicle] | Machine-checked error bounds (IID test set); per-input robustness of networks | No commit-then-sample, no rates on production pools, no tabular models |

## The recent result that matters most

Certifying a model on a fixed audit set can be gamed: one model was certified at over 99% accuracy and scored under 30% on fresh data; the fix is to commit to the model first and sample the audit data afterwards [@luck2026certified]. This is assumption A2 and the beacon-sampling protocol.

## Regulation

- PRA SS1/23, in force since May 2024: five principles, including independent validation [@pra2023ss1].
- EU AI Act: credit scoring is high-risk (Annex III 5(b)); Article 15 asks for accuracy and robustness [@euaiact2024]. The application date was unclear in the sources (August 2026 or, after the Digital Omnibus, December 2027).

## What this means for the project

Nobody offers independently re-checkable certificates for production models, with assumptions stated, bound to the deployed model, covering performance, robustness, monotonicity and fairness in one framework. Full comparison, today and in the vision: `docs/positioning.md`. First milestone: see `docs/PLAN.md`, "Milestone: certified credit-model report".
