import Hironaka

/-!
# Resolution's formalization of Hironaka's theorem

The whole library `Hironaka` of `resolutionorg/hironaka` (tag `v4.34.0`, pinned in `lakefile.lean`):
resolution of singularities in characteristic zero for schemes, analytic manifolds and analytic
spaces. `tests/HironakaSmoke.lean` lists its main theorems with their axioms.

The singular learning theory files import only the analytic form they use,
`Hironaka.Resolution.Standard.Analytic` (`formal/core/LearningTheory/Singular/Resolution.lean`).
-/
