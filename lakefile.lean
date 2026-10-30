import Lake
open Lake DSL

package «open_theory» where
  -- Lean / Mathlib 4.34.0. Blueprint lives in blueprint/ (leanblueprint).

-- formal/: the mathematics, the claim templates and the soundness of every check.
-- `OpenTheory` is the root module (formal/OpenTheory.lean); `Core` owns formal/core/<Layer>/:
-- Foundations → Models → Properties → Theory → Scopes → Specs, each importing only the layers
-- before it (tests/regression/check_layers.py).
@[default_target]
lean_lib «OpenTheory» where
  srcDir := "formal"

lean_lib «Core» where
  srcDir := "formal/core"
  globs := #[`Foundations, `Models, `Properties, `Theory, `Scopes, `Specs].map .andSubmodules

-- examples/: kernel-checked certificate instances (generated data + one theorem each).
@[default_target]
lean_lib «CertifiedDigits» where
  srcDir := "examples/certified_accuracy/lean"

require TorchLean from git
  "https://github.com/lean-dojo/TorchLean.git" @ "2d148d85839d97b02b06e8e02be61e3d57be3ad7"

-- Resolution's Hironaka formalization, tag `v4.34.0` (same Mathlib commit as ours).
-- The whole library is imported by `formal/core/Foundations/Hironaka.lean`.
require hironaka from git
  "https://github.com/resolutionorg/hironaka.git" @ "a0d237580a68818b5142b6d404a2670b3fcee697"

-- Keep Mathlib last: its support-package revisions take precedence.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"

lean_exe audit_axioms where
  root := `verifier.backends.formal.audit_axioms

-- Narrow, provenance-recorded FoML port for the pinned Mathlib version.
lean_lib FoML where
  srcDir := "formal/vendors/FoML"

-- Narrow, provenance-recorded StatLean port for finite-class PAC bounds.
lean_lib StatLean where
  srcDir := "formal/vendors/StatLean"

-- Narrow, provenance-recorded SLT port: matrix perturbation infrastructure
-- (Courant–Fischer, Eckart–Young–Mirsky, Weyl, Davis–Kahan).
lean_lib SLT where
  srcDir := "formal/vendors/SLT"
