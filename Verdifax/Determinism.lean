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

/-! ### Manifest binding

The headline theorem: under collision-freedom and the null-free byte
discipline, equal sealed manifest hashes force identical admitted
inputs AND identical outcomes. The manifest hash binds every governed
fact; nothing can be swapped behind it. -/

/-- A single non-null byte is a null-free field. -/
theorem singleton_nullFree {b : UInt8} (hb : ¬ sep = b) : NullFree [b] := by
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hb hmem

/-- Null-freedom of the outcome-dependent manifest fields. -/
def NullFreeResult : RunResult → Prop
  | .completed t out _ => NullFree t ∧ NullFree out
  | .halted t pout _   => NullFree t ∧ NullFree pout
  | .denied r          => NullFree r

/-- A run whose hash and kernel emit null-free bytes yields null-free
    outcome fields. Models the production convention that digests and
    outputs embedded in preimages are hex-encoded. -/
theorem run_nullFreeResult (H : Bytes → Bytes) (p : Policy) (k : Kernel)
    (i : AdmittedInput) (hH : ∀ x, NullFree (H x))
    (hk : ∀ x, NullFree (k x).1) :
    NullFreeResult (run H p k i) := by
  unfold run
  split
  case h_1 r heq =>
    unfold gate at heq
    split at heq
    case inl hp => exact heq.elim
    case inr hp =>
      injection heq with hr
      show NullFree r
      rw [← hr]
      exact hH _
  case h_2 tok heq =>
    have htok : NullFree tok := by
      unfold gate at heq
      split at heq
      case inr hp => exact heq.elim
      case inl hp =>
        injection heq with h'
        rw [← h']
        exact hH _
    split
    next out' cost' hkeq =>
      have hout : NullFree out' := by
        have h1 : (k i.payload).1 = out' := by rw [hkeq]
        rw [← h1]
        exact hk _
      split <;> exact ⟨htok, hout⟩

/-- Well-formed inputs and null-free outcomes give a null-free
    manifest. -/
theorem manifestFields_allNullFree (i : AdmittedInput) (hi : WellFormed i)
    (r : RunResult) (hr : NullFreeResult r) :
    AllNullFree (manifestFields i r) := by
  cases r with
  | completed t out cost =>
    obtain ⟨ht, hout⟩ := hr
    intro x hx
    simp only [manifestFields, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hx
    · exact hi.versionTag
    · exact singleton_nullFree (by decide)
    · exact hi.policyId
    · exact hi.payload
    · exact hi.actorKeyId
    · exact hi.adapterId
    · exact hi.ledgerNonce
    · exact natField_nullFree _
    · exact ht
    · exact hout
    · exact natField_nullFree _
  | halted t pout cost =>
    obtain ⟨ht, hpout⟩ := hr
    intro x hx
    simp only [manifestFields, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hx
    · exact hi.versionTag
    · exact singleton_nullFree (by decide)
    · exact hi.policyId
    · exact hi.payload
    · exact hi.actorKeyId
    · exact hi.adapterId
    · exact hi.ledgerNonce
    · exact natField_nullFree _
    · exact ht
    · exact hpout
    · exact natField_nullFree _
  | denied r =>
    intro x hx
    simp only [manifestFields, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hx
    · exact hi.versionTag
    · exact singleton_nullFree (by decide)
    · exact hi.policyId
    · exact hi.payload
    · exact hi.actorKeyId
    · exact hi.adapterId
    · exact hi.ledgerNonce
    · exact natField_nullFree _
    · exact hr

/-- The manifest field list is never empty. -/
theorem manifestFields_ne_nil (i : AdmittedInput) (r : RunResult) :
    manifestFields i r ≠ [] := by
  cases r with
  | completed t out cost => exact fun h => nomatch h
  | halted t pout cost => exact fun h => nomatch h
  | denied r => exact fun h => nomatch h

/-- **Manifest binding.** Two governed runs (possibly under different
    policies and kernels) with equal sealed manifest hashes have
    identical admitted inputs and identical outcomes, assuming no hash
    collision and the null-free byte discipline. This is the formal
    core of the audit-of-record claim: the manifest hash binds the
    version, payload, policy identity, actor, adapter, nonce, budget,
    outcome shape, output bytes, and cost, all at once. -/
theorem manifest_binding (H : Bytes → Bytes) (hH : CollisionFree H)
    (hHnf : ∀ x, NullFree (H x))
    (p q : Policy) (k l : Kernel)
    (hk : ∀ x, NullFree (k x).1) (hl : ∀ x, NullFree (l x).1)
    (i j : AdmittedInput) (hi : WellFormed i) (hj : WellFormed j)
    (h : sealRun H p k i = sealRun H q l j) :
    i = j ∧ run H p k i = run H q l j := by
  have hm : manifestFields i (run H p k i) = manifestFields j (run H q l j) :=
    encode_injective _ _
      (manifestFields_allNullFree i hi _ (run_nullFreeResult H p k i hHnf hk))
      (manifestFields_allNullFree j hj _ (run_nullFreeResult H q l j hHnf hl))
      (manifestFields_ne_nil i _) (manifestFields_ne_nil j _)
      (hH _ _ h)
  cases hri : run H p k i with
  | completed t1 out1 c1 =>
    cases hrj : run H q l j with
    | completed t2 out2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      injection hm with h3 hm
      injection hm with h4 hm
      injection hm with h5 hm
      injection hm with h6 hm
      injection hm with h7 hm
      injection hm with h8 hm
      injection hm with h9 hm
      injection hm with h10 hm
      injection hm with h11 hm
      have hbl := natField_injective h8
      have hc := natField_injective h11
      refine ⟨?_, ?_⟩
      · have hmk :
            AdmittedInput.mk i.versionTag i.payload i.policyId i.actorKeyId
              i.adapterId i.ledgerNonce i.budgetLimit
            = AdmittedInput.mk j.versionTag j.payload j.policyId j.actorKeyId
              j.adapterId j.ledgerNonce j.budgetLimit := by
          rw [h1, h4, h3, h5, h6, h7, hbl]
        exact hmk
      · rw [h9, h10, hc]
    | halted t2 pout2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
    | denied r2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
  | halted t1 pout1 c1 =>
    cases hrj : run H q l j with
    | completed t2 out2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
    | halted t2 pout2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      injection hm with h3 hm
      injection hm with h4 hm
      injection hm with h5 hm
      injection hm with h6 hm
      injection hm with h7 hm
      injection hm with h8 hm
      injection hm with h9 hm
      injection hm with h10 hm
      injection hm with h11 hm
      have hbl := natField_injective h8
      have hc := natField_injective h11
      refine ⟨?_, ?_⟩
      · have hmk :
            AdmittedInput.mk i.versionTag i.payload i.policyId i.actorKeyId
              i.adapterId i.ledgerNonce i.budgetLimit
            = AdmittedInput.mk j.versionTag j.payload j.policyId j.actorKeyId
              j.adapterId j.ledgerNonce j.budgetLimit := by
          rw [h1, h4, h3, h5, h6, h7, hbl]
        exact hmk
      · rw [h9, h10, hc]
    | denied r2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
  | denied r1 =>
    cases hrj : run H q l j with
    | completed t2 out2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
    | halted t2 pout2 c2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      exact absurd h2 (by decide)
    | denied r2 =>
      rw [hri, hrj] at hm
      simp only [manifestFields] at hm
      injection hm with h1 hm
      injection hm with h2 hm
      injection hm with h3 hm
      injection hm with h4 hm
      injection hm with h5 hm
      injection hm with h6 hm
      injection hm with h7 hm
      injection hm with h8 hm
      injection hm with h9 hm
      have hbl := natField_injective h8
      refine ⟨?_, ?_⟩
      · have hmk :
            AdmittedInput.mk i.versionTag i.payload i.policyId i.actorKeyId
              i.adapterId i.ledgerNonce i.budgetLimit
            = AdmittedInput.mk j.versionTag j.payload j.policyId j.actorKeyId
              j.adapterId j.ledgerNonce j.budgetLimit := by
          rw [h1, h4, h3, h5, h6, h7, hbl]
        exact hmk
      · rw [h9]

end Verdifax
