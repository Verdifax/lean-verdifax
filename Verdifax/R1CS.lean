-- Verdifax R1CS model: rank-1 constraint systems and satisfiability.
--
-- HONEST BOUNDARY: this file proves STRUCTURAL lemmas about R1CS
-- (composition and decidability of satisfiability), the layer the ZKSP
-- chain's constraint encoding lives at. It does NOT prove, claim, or
-- imply any zero-knowledge property; the real ZK prover (winterfell
-- STARK/FRI) remains a scaffold, disclosed as such on the roadmap and
-- in every audit bundle. Constraints are modelled over Nat, a
-- commutative semiring: the lemmas below need no multiplicative
-- inverses, so nothing here depends on field structure. The production
-- system's prime-field arithmetic is deliberately out of scope.

namespace Verdifax.R1CS

/-- Dot product of a coefficient row with a witness vector. Missing
    entries on either side are treated as zeros (standard padding
    convention). -/
def dot : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, z :: zs => a * z + dot as zs

theorem dot_nil_left (z : List Nat) : dot [] z = 0 := rfl

theorem dot_nil_right (a : List Nat) : dot a [] = 0 := by
  cases a <;> rfl

/-- A rank-1 constraint: three coefficient rows demanding
    (a · z) * (b · z) = (c · z). -/
structure Constraint where
  a : List Nat
  b : List Nat
  c : List Nat

/-- A witness satisfies a constraint when the rank-1 equation holds. -/
def satisfies (z : List Nat) (con : Constraint) : Prop :=
  dot con.a z * dot con.b z = dot con.c z

instance (z : List Nat) (con : Constraint) : Decidable (satisfies z con) :=
  inferInstanceAs (Decidable (dot con.a z * dot con.b z = dot con.c z))

/-- A witness satisfies a system when it satisfies every constraint. -/
def SatSystem (z : List Nat) (S : List Constraint) : Prop :=
  ∀ con, con ∈ S → satisfies z con

/-- The empty system is satisfied by any witness. -/
theorem satSystem_nil (z : List Nat) : SatSystem z [] :=
  fun _ h => nomatch h

/-- Satisfying a system decomposes constraint by constraint. -/
theorem satSystem_cons {z : List Nat} {c : Constraint} {S : List Constraint} :
    SatSystem z (c :: S) ↔ satisfies z c ∧ SatSystem z S := by
  constructor
  · intro h
    exact ⟨h c (List.Mem.head _), fun d hd => h d (List.Mem.tail _ hd)⟩
  · intro ⟨hc, hS⟩ d hd
    cases hd with
    | head => exact hc
    | tail _ hmem => exact hS d hmem

/-- **Gadget composition.** A witness satisfies the concatenation of
    two constraint systems exactly when it satisfies both. This is the
    lemma that justifies building larger circuits from verified
    gadgets: composition can neither create nor mask violations. -/
theorem satSystem_append {z : List Nat} {S T : List Constraint} :
    SatSystem z (S ++ T) ↔ SatSystem z S ∧ SatSystem z T := by
  induction S with
  | nil =>
    constructor
    · intro h
      exact ⟨satSystem_nil z, h⟩
    · intro ⟨_, hT⟩
      exact hT
  | cons c S ih =>
    constructor
    · intro h
      obtain ⟨hc, hrest⟩ := satSystem_cons.mp h
      obtain ⟨hS, hT⟩ := ih.mp hrest
      exact ⟨satSystem_cons.mpr ⟨hc, hS⟩, hT⟩
    · intro ⟨hcS, hT⟩
      obtain ⟨hc, hS⟩ := satSystem_cons.mp hcS
      exact satSystem_cons.mpr ⟨hc, ih.mpr ⟨hS, hT⟩⟩

/-- Known-answer check: the multiplication gadget x * y = out is
    satisfied by the witness (1, x = 3, y = 4, out = 12), wire order
    [one, x, y, out]. Kernel-evaluated. -/
example :
    satisfies [1, 3, 4, 12]
      ⟨[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]⟩ := by decide

/-- Negative known-answer: the same gadget rejects out = 13. -/
example :
    ¬ satisfies [1, 3, 4, 13]
      ⟨[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]⟩ := by decide

end Verdifax.R1CS
