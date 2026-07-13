-- Lake build file for the Verdifax Lean 4 formal-verification
-- development. Empty placeholder library for Phase 5; Phase 6
-- populates Verdifax/Pipeline.lean, Verdifax/Canonical.lean,
-- Verdifax/R1CS.lean, and Verdifax/Determinism.lean against the
-- module exposed here.
--
-- Build with:
--
--   elan toolchain install leanprover/lean4:v4.8.0
--   lake build
--
-- The pinned toolchain version (lean-toolchain in this directory)
-- matches the EXPECTED_DETERMINISM_THEOREM_TYPE_HASH the Rust
-- adapter at ../ZKSP/src/l10/lean_adapter.rs binds against. Bumping
-- the toolchain requires a coordinated update of that adapter's
-- frozen type-hash so Phase 6 verifiers continue to pin against the
-- same theorem signature across builds.

import Lake
open Lake DSL

package «verdifax» where
  -- Package-level Lake settings. Phase 6 may add `leanOptions` for
  -- compile-time settings (e.g. `pp.deepTerms false`); none required
  -- for the empty placeholder.
  -- Mathlib is the standard math library; pinned by `require` below.
  precompileModules := false

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib «Verdifax» where
  -- Library defaults are fine. Phase 6 fills in:
  --   • Verdifax.Canonical   — RFC 8785 + SHA-256 model
  --   • Verdifax.Pipeline    — L0 to L6 as a pure function
  --   • Verdifax.R1CS        — R1CS satisfiability lemmas
  --   • Verdifax.Determinism — pipeline_determinism theorem
  --
  -- Until those modules ship, `lake build` against this empty
  -- library succeeds and exercises only the toolchain wiring.
  roots := #[`Verdifax]
