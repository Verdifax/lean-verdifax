-- Verdifax pipeline invariants.
--
-- HONEST BOUNDARY: every theorem below is about the model in
-- Verdifax/Pipeline.lean, not about the Go binary in production. See
-- the boundary note at the top of that file.

import Verdifax.Pipeline

namespace Verdifax

/-- Null-freedom of every admitted byte field. Models the production
    canonicalization discipline: byte fields embedded in preimages are
    hex-encoded (or otherwise escaped) and never contain the null
    separator. -/
structure WellFormed (i : AdmittedInput) : Prop where
  versionTag  : NullFree i.versionTag
  payload     : NullFree i.payload
  policyId    : NullFree i.policyId
  actorKeyId  : NullFree i.actorKeyId
  adapterId   : NullFree i.adapterId
  ledgerNonce : NullFree i.ledgerNonce

/-- Numeric manifest fields never contain the separator. -/
theorem natField_nullFree (n : Nat) : NullFree (natField n) := by
  induction n with
  | zero =>
    intro h
    have h' : sep ∈ ([] : Bytes) := h
    nomatch h'
  | succ m ih =>
    intro h
    have h' : sep ∈ (0x31 :: natField m : Bytes) := h
    simp only [List.mem_cons] at h'
    cases h' with
    | inl h'' => exact absurd h'' (by decide)
    | inr h'' => exact ih h''

/-- Numeric manifest fields bind their value injectively. -/
theorem natField_injective {n m : Nat} (h : natField n = natField m) : n = m := by
  have hlen := congrArg List.length h
  simpa [natField] using hlen

/-- **Pipeline determinism.** Same policy, same kernel, same admitted
    input: same sealed manifest hash. In a pure-functional model this
    is congruence, and this docstring says so plainly; the theorem's
    value is its STATEMENT, which fixes the complete dependency set of
    the sealed manifest. The model has no clock, no random state, no
    ambient environment: if the real pipeline reads anything not
    listed in `AdmittedInput` (plus the policy and kernel), it has
    diverged from the verified model. That enumeration is the
    specification-level counterpart of the Gate-4 `time.Now()`
    regression fix. -/
theorem pipeline_determinism (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    {i j : AdmittedInput} (h : i = j) :
    sealRun H p k i = sealRun H p k j := by
  rw [h]

/-- **Gate soundness, completed path.** A completed run implies the
    policy passed, the token is exactly the sealed AllowToken, the
    output and cost are the kernel's, and the budget was respected.
    There is no path to a completed record around the gate. -/
theorem run_completed_sound (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    (i : AdmittedInput) {t out : Bytes} {cost : Nat}
    (h : run H p k i = .completed t out cost) :
    p i = true ∧ t = allowToken H i ∧ (out, cost) = k i.payload
      ∧ ¬ i.budgetLimit < cost := by
  unfold run at h
  split at h
  case h_1 r heq => injection h
  case h_2 tok heq =>
    unfold gate at heq
    split at heq
    case inr hp => exact heq.elim
    case inl hp =>
      injection heq with htok
      split at h
      next out' cost' hkeq =>
        split at h
        case inl hb => exact h.elim
        case inr hb =>
          injection h with h1 h2 h3
          refine ⟨hp, ?_, ?_, ?_⟩
          · exact (htok.trans h1).symm
          · rw [← h2, ← h3]; exact hkeq.symm
          · rw [← h3]; exact hb

/-- **Halt preservation.** A halted run implies the policy passed, the
    halt result carries the ORIGINAL sealed AllowToken, the partial
    output and cost are the kernel's, and the budget was in fact
    exceeded. Budget halts cannot forge or drop the admission token. -/
theorem run_halted_sound (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    (i : AdmittedInput) {t pout : Bytes} {cost : Nat}
    (h : run H p k i = .halted t pout cost) :
    p i = true ∧ t = allowToken H i ∧ (pout, cost) = k i.payload
      ∧ i.budgetLimit < cost := by
  unfold run at h
  split at h
  case h_1 r heq => injection h
  case h_2 tok heq =>
    unfold gate at heq
    split at heq
    case inr hp => exact heq.elim
    case inl hp =>
      injection heq with htok
      split at h
      next out' cost' hkeq =>
        split at h
        case inr hb => exact h.elim
        case inl hb =>
          injection h with h1 h2 h3
          refine ⟨hp, ?_, ?_, ?_⟩
          · exact (htok.trans h1).symm
          · rw [← h2, ← h3]; exact hkeq.symm
          · rw [← h3]; exact hb

/-- **Gate soundness, denied path.** A denied run implies the policy
    failed and the receipt is exactly the sealed DenyReceipt for the
    recorded reason. Denials are sealed evidence, not silent drops. -/
theorem run_denied_sound (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    (i : AdmittedInput) {r : Bytes}
    (h : run H p k i = .denied r) :
    p i = false ∧ r = denyReceipt H i reasonPolicyDenied := by
  unfold run at h
  split at h
  case h_2 tok heq =>
    split at h
    next out' cost' hkeq =>
      split at h
      case inl hb => exact h.elim
      case inr hb => exact h.elim
  case h_1 rcpt heq =>
    injection h with hr
    unfold gate at heq
    split at heq
    case inl hp => exact heq.elim
    case inr hp =>
      injection heq with hrcpt
      have hpf : p i = false := by
        cases hpv : p i with
        | true => exact absurd hpv hp
        | false => rfl
      exact ⟨hpf, (hrcpt.trans hr).symm⟩

end Verdifax
