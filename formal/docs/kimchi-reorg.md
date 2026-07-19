# Kimchi reorganization — target structure

A planning document (not yet executed). Reorganizes the `Kimchi` package around the
same axis the `bulletproof-pcs` reorg used: **the idealized polynomial protocol and its
soundness (Side A)** vs **the concrete PCS instantiation and its soundness (Side B)**. The
boundary is exactly *"does it mention commitments / the Poseidon sponge / the Fiat–Shamir
axiom?"* — everything below is axiom-free polynomial math; everything above is the
instantiation where the assumptions (FS axiom, DL-binding) live.

Organization is the primary axis; privatization and the doc pass are layered on top
afterward, once each file's concern is settled.

## Side A — the idealized polynomial protocol & its soundness

Pure polynomials, evaluations, and the abstract relation `Satisfies`. No commitments, no
sponge, no FS axiom, no `Bulletproof`.

### `Kimchi/Gate/` — the gate primitives

Each gate splits into its **definition** and its **semantics** (faithfulness — the gate
computes the intended elliptic-curve operation over Mathlib's group law). Row-level and
chain-level faithfulness are the same concern, so the chain circuits (`Circuit/`) fold into
each gate's `Semantics`.

| new file | from | contents |
| --- | --- | --- |
| `Gate/AddComplete.lean` | `Gate/AddComplete.lean` [38–142] | `Witness`, `Holds`, `ok`, `ok_iff` |
| `Gate/Semantics/AddComplete.lean` | `Gate/AddComplete.lean` [144–] | `sound_*`, `complete_*` |
| `Gate/VarBaseMul.lean` | `Gate/VarBaseMul.lean` [60–506] | definition |
| `Gate/Semantics/VarBaseMul.lean` | `Gate/VarBaseMul.lean` [507–] + `Circuit/VarBaseMul{.lean,/Internal.lean}` | row + ladder chain (~1600L, one file, private internals) |
| `Gate/EndoMul.lean` / `Gate/Semantics/EndoMul.lean` | `Gate/EndoMul.lean` + `Circuit/EndoMul{.lean,/Internal.lean}` | def / row + chain |
| `Gate/EndoScalar.lean` / `Gate/Semantics/EndoScalar.lean` | `Gate/EndoScalar.lean` + `Circuit/EndoScalar{.lean,/Internal.lean}` | def / row + chain |
| `Gate/Generic.lean` / `Gate/Semantics/Generic.lean` | `Gate/Generic.lean` | def / semantics |
| `Gate/Poseidon.lean` / `Gate/Semantics/Poseidon.lean` | `Gate/Poseidon.lean` | def / semantics |

The Pasta EC-gate corollaries (`pallas_endoMul`, `varBaseMul_scaleFast1`, …) are the
gate/chain semantics at the concrete curve — they stay in `Semantics/`, still tracked by
the axiom gate.

### `Kimchi/Index/` — the arithmetization (stays)

`Basic` (circuit as data), `Satisfies` (the relation), `Aggregate` (the aggregate family),
`Degree` (degree bounds). `Index/Soundness` ("quotient soundness at the index") is PIOP
soundness → **move to `Quotient/Soundness.lean`** (or fold into `Quotient/`).

### `Kimchi/Quotient/` — the polynomial IOP (stays)

The vanishing/divisibility argument, the permutation/copy argument, Schwartz–Zippel. 18
files, each a genuine concept (6 uniform gate-lifts + the permutation development + the SZ
counting toolkit). Minor de-fragmentation of the tiny files (`Aggregate` 44L, `Accumulator`
79L, `Shifted` 72L) is optional and low priority.

### `Kimchi/Protocol/` — the ideal verifier & interactive soundness (NEW; moved out of `Verifier/`)

The IOP verifier's polynomial identity and the interactive-soundness result — no
commitments or FS, so it belongs on Side A, not with the concrete verifier.

| new file | from |
| --- | --- |
| `Protocol/Equation.lean` | `Verifier/Equation.lean` (the verifier equation / honest evaluation record) |
| `Protocol/Linearization.lean` | `Verifier/Linearization.lean` (the scalar side, closed form) |
| `Protocol/Soundness.lean` | `Verifier/KimchiSound.lean` (`kimchiProof_sound_of_openings`: openings + identity at good challenges ⟹ `Satisfies`) + the idealized composition `KimchiBundle`/`kimchiBundle_sound` (from `Verifier/Capstone.lean` §170–250) |

Dir name: `Protocol/`.

## Side B — the concrete PCS instantiation & its soundness

`Kimchi/Verifier/`, purified to the executable verifier, reflection, and the terminal
composition. Where Poseidon, the IPA commitments, and the axioms enter.

| file | from | concern |
| --- | --- | --- |
| `Verifier/Kimchi.lean` | unchanged | the executable verifier (IPA + Poseidon) |
| `Verifier/Reflect.lean`, `Correspond.lean`, `Sound.lean` | unchanged | reflection: executable-accept ⟹ abstract accepting run with genuine openings (via the PCS) |
| `Verifier/Capstone.lean` | §251–715 | wire views, the grid, FS transport, the concrete & run capstones (`kimchi{V,P}_sound`, `…_run_sound`) |
| `Verifier/Algebraic.lean` | §1173–1610 | the AGM reading (`kimchiProof_sound_algebraic`, `…_algebraic_ft`) |
| `Verifier/FiatShamir.lean` | §1611–2599 | the FS-reflection discharge + the **terminal roots** (`kimchi{V,P}_run_sound_algebraic_ft`) |

The terminal theorem lives in `Verifier/FiatShamir.lean`; its trust closure (FS axiom +
DL-binding + the curve certificates) must stay byte-identical through the whole move.

### The standard-model line is CUT (not kept)

Capstone §716–1172 — the soundness-error and grid-from-density development
(`kimchiBundle_sound_error`, `kimchi{V,P}_sound_error`, `kimchiBatchAcc_of_density`,
`kimchi{V,P}_sound_density`) — is the standard-model / forking-lemma alternative to the AGM
terminal path. It is internally self-contained (nothing in the AGM/terminal path consumes
it) and is being **deleted**, along with its only support module `Quotient/Rectangle.lean`
(the forking-lemma counting toolkit, imported solely by Capstone's density section).
`Quotient/SchwartzZippel.lean` is **not** part of the cut — it is the shared counting
foundation the whole PIOP and the AGM path rest on.

Before deleting, the removed development is documented in full in
`formal/docs/standard-model-line.md` — what each root stated, the forking/density argument
structure, and the exact file/section footprint — so it can be reconstructed from git if a
standard-model soundness statement (`verify = true ⟹ Satisfies` with no AGM representations)
is ever wanted. The cut's exact extent is confirmed by a dead-code pass after removing the
roots from `roots.txt` (known members: Capstone §716–1172 + `Quotient/Rectangle.lean`; watch
for density-only helpers elsewhere).

## Execution order

1. **Cut the standard-model line** — document it in `standard-model-line.md`, remove its
   roots, delete Capstone §716–1172 + `Quotient/Rectangle.lean` (dead-code-confirmed).
   Shrinks Capstone before the split. Verify the terminal closure is unchanged.
2. **Gates split** — split each `Gate/<G>.lean` into a def module + a new
   `Gate/Semantics/<G>.lean`, folding the `Circuit/` chains into the latter. The
   `Kimchi.Gate.*` namespace is unchanged (singular `Gate/` kept); only the folded
   circuit's decls move `Kimchi.Circuit.<G>.*` → `Kimchi.Gate.<G>.*`.
   Self-contained, low risk, high clarity.
3. **Pull Side A out of `Verifier/`** — `Equation`/`Linearization`/`KimchiSound` →
   `Protocol/`, plus the `kimchiBundle_sound` composition core; `Index/Soundness` →
   `Quotient/`.
4. **Split `Capstone`** — along the concern boundary into `Capstone`/`Algebraic`/
   `FiatShamir`. Delicate: verify `#print axioms` byte-identical at each step.
5. **Privatization pass** — dir by dir, once files are stable (the concern grouping makes
   many cross-file helpers same-module). ~228 candidates; watch name-collision
   false-negatives (the `sbox`/`slot` lesson).
6. **Doc pass** — evolution/scratch scan + verbosity across the package; drop `## Contents`
   inventories.

Steps 2–4 change no declaration names, so `roots.txt` and the axiom gates stay untouched and
the terminal-theorem closure is invariant. Step 1 removes roots (the cut development) but
leaves the terminal closure invariant. Each step is its own PR.
