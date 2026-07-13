# lean-verdifax

This directory is reserved for the Lean 4 formal-verification
development that backs Verdifax's L10 status record.

## Status

**Phase 5, boundary skeleton SHIPPED (May 7, 2026).** The Rust
adapter shim that consumes this development is committed at
`../ZKSP/src/l10/lean_adapter.rs`, behind the `real_lean` Cargo
feature; `MockLeanAdapter` is the default and returns
`LeanResult::Pending` under the toolchain id
`PENDING_EXTERNAL_FORMAL_VERIFICATION`.

The Lean workspace itself is now scaffolded:

- `lean-toolchain` pins the Lean version to `leanprover/lean4:v4.8.0`
- `lakefile.lean` declares the `verdifax` package with mathlib4
  pinned at the matching version
- `Verdifax.lean` is the empty top-level module that Phase 6 fills
  in with the four canonical theorem files

A Lean engineer can clone this directory, run `elan toolchain
install leanprover/lean4:v4.8.0 && lake build`, and start adding
theorems on day one. The build will succeed against the empty
placeholder library.

See `../BUILDING DOCS/LEAN4_INTEGRATION.md` for the full plan.

## Phase 6 deliverables

When Phase 6 lands, this directory contains:

```
lean-verdifax/
├── lean-toolchain                        # leanprover/lean4:v4.8.0 (pinned)
├── lakefile.lean                         # mathlib4 dependency
├── lakemanifest.json                     # transitive lockfile
├── Verdifax.lean                         # top-level imports
├── Verdifax/
│   ├── Canonical.lean                    # RFC 8785 + SHA-256 model
│   ├── Pipeline.lean                     # L0 to L6 as a pure function
│   ├── R1CS.lean                         # R1CS satisfiability lemmas
│   └── Determinism.lean                  # pipeline_determinism theorem
└── scripts/
    └── check_determinism.lean            # prints LEAN_DETERMINISM_THEOREM_TYPE_HASH=<sha256>
```

## Why an empty placeholder

A real deployment engineer needs to know that `lean-verdifax/` is the
target location, not a deprecated artifact. Committing the README
also lets the adapter unit-test that resolves
`CARGO_MANIFEST_DIR/../lean-verdifax` succeed in CI without depending
on the Lean toolchain itself.

## Contributing pre-Phase-6

If you are picking up the formal-methods work:

1. Read `../BUILDING DOCS/LEAN4_INTEGRATION.md`.
2. Install `elan` and run `elan toolchain install leanprover/lean4:v4.8.0`.
3. Initialise the layout above with `lake init verdifax math` and
   adjust the toolchain pin.
4. Land `Pipeline.lean` first, every other file depends on the
   canonical encoding model.
5. Do **not** change the type signature of
   `Verdifax.Determinism.pipeline_determinism` after the first
   review. The Rust adapter freezes its hash via
   `EXPECTED_DETERMINISM_THEOREM_TYPE_HASH`; signature drift breaks
   the binding.
