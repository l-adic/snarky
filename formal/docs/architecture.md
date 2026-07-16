# Kimchi soundness — target architecture

A proposal for re-layering the `Kimchi` soundness proof, partially executed.

**Executed so far**: the root-list consolidation (superseded milestones demoted, dead
curve-AGM/`ftQuotient` code deleted), and the package split — `pasta` (curve trust base),
`poseidon` (sponge spec + fixture kit), `bulletproof-pcs` (the IPA PCS + FS instantiation)
are now standalone lake packages; the unused ironwood vendor dependency is dropped.
**Remaining**: the privatization pass and the `Verifier/` (linearization / interactive /
FS-reflection) split described below.

## The idea

PLONK factors into three components — **arithmetization**, a **polynomial IOP**, and a
**polynomial commitment scheme** — which compose into an interactive protocol; the
**Fiat–Shamir** transform makes it non-interactive. The proof should read the same way.

Two tiers:

- **Generic core** — field-generic, no Pasta, no Poseidon. The protocol and its soundness.
- **Concrete tip** — Pasta + Poseidon. Only where it is *earned*: the executable verifier we
  run against fixtures, the sponge validated against real vectors, the curve axioms, and the
  headline "the deployed verifier is sound."

Everything generic that currently names a Pasta curve is a leak to fix. The audit says the
bottom is already close: the PCS is fully generic, the PIOP and arithmetization are generic,
and the EC gates already isolate Pasta behind a thin top-level file. The mixing is
concentrated in `Verifier/`.

## Layers

Each layer exposes an **interface** (what the layer above may use) and states its
**assumptions**. A layer never reaches past the one below it.

> **On "exposes".** Prefer Lean's `private` — it is compiler-enforced. The catch is that it
> is *file-scoped*: a `private` declaration is invisible by name in every other file and fully
> usable within its own. So make every file-local helper `private`, and keep a layer to a
> single file (interface + private helpers) wherever the proof size allows — then `private`
> enforces the whole boundary.
>
> `private` cannot express "public within these files, hidden outside," so a layer that
> genuinely spans several files and shares helpers across them (PCS, PIOP) falls back to
> convention: put the guts in an `Internal` module, have the layer above import only the
> interface module, so a leak shows up as an import of someone's `Internal`. `roots.txt` is
> the declared public surface. Reach for this only when multi-file sharing forces it.

### 0 · Substrate — `Pasta/`, `Curve`, `Shifted`, `Cycle/`
Fields, curves, the two-field cycle. Cross-cutting foundation, not part of the protocol
decomposition. Stays as is.

### 1 · Arithmetization — `Gate/`, `Circuit/`, `Index/`
- **Exposes** — `Index F n` (the circuit as data), `Satisfies idx pub wTab` (the relation the
  whole proof is *about*), the gate predicates, and gate faithfulness (`Gate.<G>.sound`: a
  satisfying row computes the intended elliptic-curve operation).
- **Assumes** — nothing; field-generic. Faithfulness is checked against Mathlib's group law.
- **Status** — generic already. The Pasta EC-gate corollaries (`pallas_endoMul`, …) live in
  the thin top-level files and belong to the concrete tip.

### 2 · Polynomial IOP — `Quotient/`
- **Exposes** — the reduction *`Satisfies` ⟺ a polynomial identity*: the constraint family is
  divisible by the vanishing polynomial iff every row satisfies, and (Schwartz–Zippel) the
  identity at a challenge outside a small bad set forces `Satisfies`.
- **Assumes** — nothing; field-generic.
- **Status** — generic. Counting-SZ (`SZ.badComb`) is the shared engine.

### 3 · PCS — `Commitment/IPA/`
- **Exposes** — `commit`, the opening relation, opening soundness (`ipa_soundnessA`: an
  accepting opening yields a witness whose evaluation is the claimed one), and binding.
- **Assumes** — DL-binding (a hypothesis, `hbind`) and an abstract accepting transcript.
- **Status** — fully generic already (0 Pasta references).

### 4 · Linearization — *(new home; today in `Linearization` + `Sound` + `Capstone`)*
The seam where kimchi couples the IOP and the PCS: the verifier never opens the quotient
directly, only through the Maller `ft` commitment.
- **Exposes** — `ft_identity_of_chunks`: the committed quotient chunks plus one `ft` opening
  yield the genuine degree-`<7n` quotient and the identity at ζ.
- **Assumes** — DL-binding (through commitment binding).
- **Status** — proven, but scattered. Deserves its own module.

### 5 · Interactive protocol — `KimchiSound`, `Equation`
- **Exposes** — `kimchiProof_sound_of_openings`: genuine per-row openings plus the `ft`/quotient
  identity at good challenges ⟹ `Satisfies`. This *is* the interactive-SNARK soundness, with
  the challenges as inputs.
- **Assumes** — DL-binding; the SZ bad-set conditions; the key/circuit correspondence.
- **Status** — proven and field-generic; the core to preserve.

### 6 · Fiat–Shamir → non-interactive — `Reflect`, `Reflection`, `Sponge/`, `Kimchi`
- **Exposes** — the reflected run (`kimchiVerify_reflects`: an accepted run *is* its own
  accepted batch, read off the code), and the FS assumption bridging acceptance to an accepting
  transcript.
- **Assumes** — the Fiat–Shamir axiom (the sponge behaves as a random oracle). Abstract here;
  concrete at the tip.
- **Status** — present but tangled with the executable verifier and the barycentric plumbing.

## The terminal theorem, recomposed

The endpoint should read as one composition down the layers:

```
kimchiVerify … = true
  ⟶ (FS)             the reflected run: its own accepted batch, sponge challenges
  ⟶ (PCS)            genuine openings of every batch row        -- ipa_soundnessA + eval_pins
  ⟶ (Linearization)  the ft opening pins the quotient identity  -- ft_identity_of_chunks
  ⟶ (Interactive)    openings + identity at good challenges     -- kimchiProof_sound_of_openings
  ⟶ (Arith/IOP)      ∃ wTab, Satisfies idx (pubView idx pub) wTab
```

Today this lives inline in `Capstone.lean` (165 KB), reaching directly into `batchC`,
`eval_pins`, `ft_identity_of_chunks`, and the reflected run. Encapsulation means the capstone
calls each layer only through its interface.

## Concrete tip

Field-generic core, specialized once per curve. Everything here is Pasta/Poseidon *for a
reason*:

- the executable verifier `kimchiVerify` over `IpaVesta`/`IpaPallas` — to run against fixtures;
- the Poseidon sponge — validated against production vectors (the FS instantiation);
- the `hasse` / CM axioms — the concrete curve;
- `ft_opening_of_reflected_{vesta,pallas}` and the two terminal theorems
  `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`;
- EC-gate faithfulness at Pasta (`pallas_endoMul`, `vesta_endoMul`, …).

## Roots to collapse

The tracked "headline" set (`roots.txt`) accreted one root per development milestone. Against
the terminal theorem, most of the verifier line is scaffolding:

- **grid** — `kimchiProof_sound`, `kimchiBundle_sound`, `kimchi{V,P}_sound`, `…_run_sound`
- **density** — `kimchi{V,P}_sound_density`, `exists_rectangle`, `card_heavyRows`, …
- **error** — `kimchiBundle_sound_error`, `kimchi{V,P}_sound_error`
- **abstract-algebraic intermediates** — `kimchiProof_sound_algebraic(_ft)`,
  `kimchi{V,P}_sound_algebraic(_ft)`

Target headline set: **one interface per layer** + the **two terminal theorems** + the
**EC-gate faithfulness at Pasta**. The precise cut is mechanical: trim `roots.txt` to that set,
run the dead-code pass, delete only what it proves dead, keep what is shared infrastructure.

## Open decision

The grid / density / error lines are not wrong — they are the **standard-model** path, the
**forking-lemma** combinatorics, and the **quantitative `B/|F|`** bound. Rejected as the
*endpoint*, not as mathematics.

- **Preserve** — keep them as a labeled alternative development, off the terminal path.
- **Cut** — delete them; the AGM terminal theorem is the sole soundness statement.

This choice sets how much collapses. Everything else in this document is independent of it.

## Migration

- One layer boundary at a time, bottom-up; the 117-root axiom gate stays green at every step.
- Reuse the EC gates' two-file discipline for the concrete tip.
- Split `Capstone.lean` last, once the interfaces below it have homes.
