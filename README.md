# lean-verdifax

Machine-checked formal-verification development for
[Verdifax](https://verdifax.com), the cryptographic audit-of-record
system for high-stakes AI decisions.

This repository contains the Lean 4 proofs that back the
`formal_verification` record sealed into every Verdifax audit bundle.
When a bundle is verified with the open-source
[`verdifax-verify`](https://github.com/Verdifax/verdifax-verify) CLI,
the `Formal verify: bound` line cites this repository and a pinned
commit. This is the source you can read to check that claim yourself.

## What is proven

The theorems (in `Verdifax/`) are kernel-checked statements about
Verdifax's **canonical preimage encoder** (the null-separated
`version ␀ field₁ ␀ field₂ …` construction that every kernel hashes
with SHA-256) and about a pure-functional **model of the pipeline**
(policy gate, budget check, manifest assembly).

- **Canonical.lean**: determinism, byte-level spec conformance, order
  sensitivity, boundary cases, **injectivity** (no two distinct
  null-free field lists share an encoding), **version binding**, and
  the lifting of all guarantees to the hash layer under an explicit
  collision-freedom assumption.
- **Pipeline.lean**: the `AdmittedInput` record (an exhaustive
  enumeration of every fact the sealed manifest depends on), the
  policy gate, the budget check, and manifest assembly.
- **Determinism.lean**: `pipeline_determinism`, gate soundness
  (completed / denied), halt preservation, and **`manifest_binding`**:
  equal sealed manifests force identical admitted inputs *and*
  outcomes, under collision-freedom.
- **R1CS.lean**: rank-1 constraint-system model with satisfiability
  and gadget-composition lemmas (structural only; no zero-knowledge
  property is claimed).
- **AxiomAudit.lean**: prints the axiom footprint of every headline
  theorem; CI additionally rejects `sorry`, ad-hoc `axiom`
  declarations, and `native_decide`.

## Honest scope

These are theorems about a **Lean model** of the pipeline, not about
the production Go binary. Most depend on **no axioms at all**; the
rest depend only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), printed in every CI build.
Byte-format fidelity of the model to the production implementation is
disclosed as roadmap work. **No zero-knowledge property is claimed**:
the ZK prover remains a disclosed scaffold on the
[Verdifax roadmap](https://verdifax.com/roadmap).

## Reproduce it yourself

```bash
elan toolchain install leanprover/lean4:v4.8.0
lake build
```

A successful build is the Lean kernel verifying every theorem. The
pinned toolchain is in `lean-toolchain`. The development uses pure
Lean 4 core only (no Mathlib import) so the build is fast and its
trust base is minimal. CI runs `lake build` plus the axiom audit on
every commit.

## License

MIT. See [LICENSE](LICENSE).
