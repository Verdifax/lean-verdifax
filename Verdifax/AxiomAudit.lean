-- Axiom audit.
--
-- Prints the axiom footprint of every headline theorem into the build
-- log, so each CI run shows exactly what the proofs trust. Expected
-- footprint: nothing beyond Lean's three standard axioms (propext,
-- Classical.choice, Quot.sound); most theorems here use none at all.
--
-- The hard gate lives in CI: the build fails if any source file
-- contains an unproven placeholder, a compiler-trusting decision
-- procedure, or an ad-hoc axiom declaration (see the audit step in
-- .github/workflows/build.yml for the exact tokens). This file makes
-- the trust base VISIBLE; the grep makes violations FATAL.

import Verdifax.Canonical
import Verdifax.Pipeline
import Verdifax.Determinism
import Verdifax.R1CS

#print axioms Verdifax.encode_deterministic
#print axioms Verdifax.encode_injective
#print axioms Verdifax.encode_version_binding
#print axioms Verdifax.hash_deterministic
#print axioms Verdifax.hash_injective
#print axioms Verdifax.hash_version_binding
#print axioms Verdifax.pipeline_determinism
#print axioms Verdifax.run_completed_sound
#print axioms Verdifax.run_halted_sound
#print axioms Verdifax.run_denied_sound
#print axioms Verdifax.manifest_binding
#print axioms Verdifax.R1CS.satSystem_cons
#print axioms Verdifax.R1CS.satSystem_append
