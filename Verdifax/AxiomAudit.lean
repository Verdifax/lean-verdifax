-- Axiom audit.
--
-- Prints the axiom footprint of every headline theorem into the build
-- log, so each CI run shows exactly what the proofs trust. Expected
-- footprint: nothing beyond Lean's three standard axioms (propext,
-- Classical.choice, Quot.sound); most theorems here use none at all.
--
-- The hard gate lives in CI: the build fails if any source file
-- contains `sorry`, `admit`, `native_decide`, or a raw `axiom`
-- declaration. This file makes the trust base VISIBLE; the grep makes
-- violations FATAL.

import Verdifax.Canonical
import Verdifax.Pipeline
import Verdifax.Determinism

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
