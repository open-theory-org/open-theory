# SLT matrix perturbation subset

Upstream: https://github.com/YuanheZ/lean-stat-learning-theory
Revision: `d0f506f0a695018265dccb33bcb05e2f5ca1c876` (Lean 4.32.0).
License: Apache-2.0; original license preserved in `LICENSE`.
Authors (upstream): Yuanhe Zhang, Jason D. Lee, Fanghui Liu.

This directory contains the four-module import closure of
`SLT.MatrixInfra.Perturb`: singular values and singular vectors
(`Basic`), Courant–Fischer (`CourantFischer`), Eckart–Young–Mirsky (`EYM`),
and Weyl / Davis–Kahan perturbation bounds (`Perturb`). It imports only
Mathlib. The root Lake library `SLT` builds it against pinned Lean/Mathlib
4.34.0.

Compatibility change:

- `MatrixInfra/Basic.lean`, `orthonormal_leftSingularVector_of_singularValues_ne_zero`:
  Lean 4.34's `simp` no longer closes `1 = if i = i then 1 else 0` there; one
  added line `exact (ite_eq_left rfl).symm`.

The mathematical statements and proof structure are unchanged. No `sorry`,
`admit` or `axiom` occurs in these files; `#print axioms` on the main results
gives `propext`, `Classical.choice`, `Quot.sound`.

Purpose in OpenTheory: matrix perturbation tools for the statistics step of the
gradient-descent plateau theorem (`docs/slt-small-model.md`).
