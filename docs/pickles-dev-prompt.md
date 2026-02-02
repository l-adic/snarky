# Pickles Development Session Prompt

Use this prompt to start a fresh Claude Code session for pickles implementation work. It activates the relevant skills and references our planning documents.

---

## Prompt

```
I'm implementing the pickles recursive proof system in PureScript, translating from mina's OCaml implementation.

Reference our planning document at `docs/pickles-diagrams-index.md` which contains:
- Architecture diagrams for Step/Wrap computation
- TODO list with implementation checkpoints
- Source file mappings between OCaml (mina/src/lib/pickles) and our PureScript

The first TODO item is: **Validate `computeB` against Rust FFI `computeB0`**

This involves:
1. Writing a test that compares our PureScript `Commitments.computeB` against the Rust ground truth `computeB0` from `Test.Pickles.ProofFFI`
2. Using real proof data (bulletproof challenges, zeta, evalscale) extracted via FFI
3. Following the circuit testing patterns in snarky-test-utils

The `b` value formula (from wrap_deferred_values.ml) is:
```
b = challenge_poly(zeta) + r * challenge_poly(zetaOmega)
```

Please read the planning document and the relevant source files, then implement TODO 1 following our project conventions for PureScript code, tests, and FFI.
```

---

## Skills Activated

This prompt triggers:

| Skill | Activation Keywords |
|-------|---------------------|
| `project-developer-guide` | "PureScript", "tests", "FFI", "project conventions" |
| `ocaml-snarky-kimchi-translation` | "translating from mina's OCaml", "mina/src/lib/pickles" |
| `pickles-field-conventions` | "pickles", "Step/Wrap" (implicit Tick/Tock context) |

---

## Key Files to Reference

- `docs/pickles-diagrams-index.md` — Planning document with TODOs
- `docs/pickles-diagrams/*.svg` — Architecture diagrams
- `packages/pickles/src/Pickles/Commitments.purs` — Our `computeB` implementation
- `packages/pickles/test/Test/Pickles/ProofFFI.purs` — Rust FFI for `computeB0`
- `mina/src/lib/pickles/wrap_deferred_values.ml` — OCaml source for `b` computation
- `vendor/proof-systems/poly-commitment/src/commitment.rs` — Rust `b_poly` implementation
