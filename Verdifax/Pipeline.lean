-- Verdifax pipeline model.
--
-- HONEST BOUNDARY: this file models the orchestrator's pipeline as a
-- pure function in Lean. Theorems in Verdifax/Determinism.lean are
-- about THIS MODEL, not about the Go binary running in production.
-- The model earns its keep in two ways:
--
--   1. `AdmittedInput` is an exhaustive, machine-checked enumeration of
--      every fact the sealed manifest depends on. A hidden runtime
--      dependency (wall-clock time, random state) cannot enter the
--      manifest path without changing these theorem statements. This is
--      the specification-level counterpart of the Gate-4 determinism
--      regression fix (a `time.Now()` that had been seeded into the
--      manifest).
--
--   2. The structural invariants (manifest binding, gate soundness,
--      halt preservation) are genuine theorems, inherited from the
--      canonical-encoding results in Verdifax/Canonical.lean.

import Verdifax.Canonical

namespace Verdifax

/-- Every fact the sealed manifest binds. Adding a runtime dependency to
    the real pipeline without adding a field here is exactly the class
    of bug this enumeration exists to make visible. -/
structure AdmittedInput where
  versionTag  : Bytes
  payload     : Bytes
  policyId    : Bytes
  actorKeyId  : Bytes
  adapterId   : Bytes
  ledgerNonce : Bytes
  budgetLimit : Nat

/-- A policy is a pure decision over the admitted input (PSL model). -/
abbrev Policy := AdmittedInput → Bool

/-- Kernel execution model: an opaque pure function from payload to
    (output, cost). Nothing below inspects it. -/
abbrev Kernel := Bytes → Bytes × Nat

/-- Deny reason recorded by the policy gate (single non-null byte). -/
def reasonPolicyDenied : Bytes := [0x01]

/-- Outcome tags bound into the manifest so the three outcome shapes
    can never collide (single non-null bytes: 'C', 'H', 'D'). -/
def tagCompleted : Bytes := [0x43]
def tagHalted    : Bytes := [0x48]
def tagDenied    : Bytes := [0x44]

/-- Injective, null-free byte encoding of a natural number. The model
    only requires that numeric manifest fields bind their value
    injectively without containing the separator; the production byte
    format (decimal ASCII) is deliberately not modelled, because it is
    not what the binding theorems are about. -/
def natField (n : Nat) : Bytes := List.replicate n 0x31

/-- Fields bound into the AllowToken preimage. -/
def allowFields (i : AdmittedInput) : List Bytes :=
  [i.versionTag, i.policyId, i.payload, i.actorKeyId]

/-- Sealed admission token issued when the policy gate passes
    (AllowToken model). -/
def allowToken (H : Bytes → Bytes) (i : AdmittedInput) : Bytes :=
  H (encode (allowFields i))

/-- Sealed denial receipt issued when the policy gate rejects
    (DenyReceipt model). -/
def denyReceipt (H : Bytes → Bytes) (i : AdmittedInput) (reason : Bytes) : Bytes :=
  H (encode [i.versionTag, i.policyId, reason])

/-- Outcome of the policy gate. -/
inductive GateOutcome where
  | allow (token : Bytes)
  | deny  (receipt : Bytes)

/-- Pre-execution policy gate (PEPG model): every run is admitted or
    denied BEFORE any kernel executes; there is no third path. -/
def gate (H : Bytes → Bytes) (p : Policy) (i : AdmittedInput) : GateOutcome :=
  if p i then .allow (allowToken H i)
  else .deny (denyReceipt H i reasonPolicyDenied)

/-- Result of a governed run. -/
inductive RunResult where
  | completed (token output : Bytes) (cost : Nat)
  | halted    (token partialOutput : Bytes) (cost : Nat)
  | denied    (receipt : Bytes)

/-- The governed pipeline: gate, execute, budget-check (CCV model).
    A cost above the admitted budget yields a halt result that still
    carries the original admission token. -/
def run (H : Bytes → Bytes) (p : Policy) (k : Kernel) (i : AdmittedInput) : RunResult :=
  match gate H p i with
  | .deny r  => .denied r
  | .allow t =>
    match k i.payload with
    | (out, cost) =>
      if i.budgetLimit < cost then .halted t out cost
      else .completed t out cost

/-- Manifest field list: every admitted fact plus the outcome, in fixed
    order, ready for the canonical encoder. -/
def manifestFields (i : AdmittedInput) : RunResult → List Bytes
  | .completed t out cost =>
      [i.versionTag, tagCompleted, i.policyId, i.payload, i.actorKeyId,
       i.adapterId, i.ledgerNonce, natField i.budgetLimit, t, out, natField cost]
  | .halted t partialOut cost =>
      [i.versionTag, tagHalted, i.policyId, i.payload, i.actorKeyId,
       i.adapterId, i.ledgerNonce, natField i.budgetLimit, t, partialOut, natField cost]
  | .denied r =>
      [i.versionTag, tagDenied, i.policyId, i.payload, i.actorKeyId,
       i.adapterId, i.ledgerNonce, natField i.budgetLimit, r]

/-- The sealed manifest hash for a governed run. -/
def sealRun (H : Bytes → Bytes) (p : Policy) (k : Kernel) (i : AdmittedInput) : Bytes :=
  H (encode (manifestFields i (run H p k i)))

/-! Definitional lemmas exercising the gate paths. -/

theorem gate_allow_of_pass (H : Bytes → Bytes) (p : Policy) (i : AdmittedInput)
    (h : p i = true) : gate H p i = .allow (allowToken H i) := by
  simp [gate, h]

theorem gate_deny_of_fail (H : Bytes → Bytes) (p : Policy) (i : AdmittedInput)
    (h : p i = false) : gate H p i = .deny (denyReceipt H i reasonPolicyDenied) := by
  simp [gate, h]

theorem run_denied_of_fail (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    (i : AdmittedInput) (h : p i = false) :
    run H p k i = .denied (denyReceipt H i reasonPolicyDenied) := by
  simp [run, gate, h]

end Verdifax
