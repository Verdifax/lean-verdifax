-- Verdifax formal development, root module.
--
-- Pure Lean 4 core (no Mathlib import) so `lake build` verifies every
-- theorem with only the kernel and the stated axioms.
--
-- Tree layout (mirrors the roadmap's formal-verification scope):
--   Verdifax/Canonical.lean   — canonical preimage encoder: determinism,
--                               spec conformance, order sensitivity,
--                               injectivity, version binding, and the
--                               hash-layer lifting (11 theorems).
--   Verdifax/Pipeline.lean    — (next) the L0-L8 pipeline as a pure
--                               function over admitted inputs.
--   Verdifax/Determinism.lean — (next) the pipeline_determinism theorem.
--   Verdifax/R1CS.lean        — (next) R1CS satisfiability lemmas.

import Verdifax.Canonical
