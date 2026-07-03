# Breadth plan: widening the ingested checker to the rest of the kimchi gate set

**Goal.** Extend `Kimchi.Circuit`'s verified checker (and, where worthwhile, the algebraic soundness
layer) from the 7 currently-modelled gate kinds to the remaining kimchi gates Mina's *application*
circuits use — so more real dumped circuits pass the drift-guarded verified checker with no
`True`-stubs. This is orthogonal to the composition/Pickles direction: it widens *coverage of the
ingested object*, not depth of what's proven about one circuit.

## Current coverage vs. the gap

Modelled today (`GateKind` = 7): `Generic`, `Zero`, `Poseidon`, `CompleteAdd`, `VarBaseMul`,
`EndoMul`, `EndoMulScalar`. Missing kimchi gate types (from proof-systems `circuits/polynomials/`):

| Gate | proof-systems source | rows | ~constraints | lookup-entangled? |
| --- | --- | --- | --- | --- |
| `RangeCheck0` | `range_check/` | 1 | ~4 (crumbs + limb sum) | **yes** (12-bit table) |
| `RangeCheck1` | `range_check/` | 2 | ~9 | **yes** |
| `ForeignFieldAdd` | `foreign_field_add` | 1 | ~4 (limb add + carry + bound) | partial (result range-checked) |
| `ForeignFieldMul` | `foreign_field_mul` | 2 | ~20 (quotient/remainder, carries) | **yes**, heavy |
| `Xor16` | `xor` | 1 (chained) | ~3 (nibble sums) | **yes** (XOR table) |
| `Rot64` | `rotation` | 1 (+range) | ~4 | partial (excess range-checked) |
| `Lookup` | the plookup argument | — | — | *is* the lookup mechanism |

## The two-part cost per gate (and the PS dependency)

Adding a gate to the **checker** is mechanical and Lean-only:
1. add the constructor to `GateKind` (`Kimchi/Circuit.lean`);
2. new `Kimchi/Checker/<Gate>.lean` — `holds`/`ok`/`ok_iff`, transcribed from the proof-systems
   polynomial file (the established shape, cf. `Checker/VarBaseMul.lean`);
3. add the `rowHolds`/`rowOk` branch and extend `rowOk_iff`/`check_iff` (one `simp` lemma each);
4. add the `typ` string to `Kimchi.Json.kindOf`.

**Validating** it against reality (a real dumped fixture + `make lean-check-fixtures`) needs a
PureScript circuit that *emits* that gate. Today only `AddComplete/EndoMul/EndoScalar/Poseidon/
RangeCheck/VarBaseMul` gadgets exist under `packages/snarky-kimchi/.../Circuit/Kimchi/`. So for
`ForeignField*`, `Xor16`, `Rot64` a **PS gadget must be written (or a fixture hand-authored from the
Rust backend) first** — this is a real, per-gate chunk of the effort, not Lean work. (Note:
`RangeCheck.purs`'s `rangeCheck128` currently routes through `EndoScalar`, so even it may not emit
native `RangeCheck0/1` rows — confirm before assuming a free fixture.)

## The strategic fork: lookups

Most of these gates only *fully* mean what they say **because of a lookup argument** — `RangeCheck0`
is "88 bits" only via the 12-bit table; `Xor16` is "XOR" only via the XOR table; `ForeignFieldMul`
and `Rot64` lean on range-checks. Their **row constraints** (the decomposition/carry relations) are
straightforwardly modelable and give partial coverage, but **algebraic soundness** ("this really is
the XOR / really is in range") requires modeling plookup — a protocol-level multiset argument, a
separate and larger effort than any single gate.

So decide up front which target you're buying:

- **(A) Checker coverage, honest about the lookup gap.** Model each gate's *row constraints* only.
  `check` accepts real circuits using these gates; document that range/XOR *enforcement* is deferred
  to the (unmodelled) lookup argument. Cheap, unblocks ingesting real application circuits.
- **(B) Real soundness.** Model the plookup argument first (its own project), *then* each
  arithmetic gate's soundness composes the row constraints with lookup membership. Principled but
  front-loads a big dependency.

Recommendation: **do (A) now, treat lookups as a separate track.** The checker's value (drift-guard
+ no stubs over more real circuits) is real even without lookup soundness, and it mirrors how the
project already ships: transcribe the constraint row, reflect it, validate against a dump.

## Phasing (path A)

**Phase 0 — pick the target circuit.** Decide whether "breadth" means *pickles* circuits (which
mostly don't use these gates — EC+Poseidon+Generic) or *application* circuits (ECDSA/keccak/
foreign-field — the real consumers). This changes which gates matter first.

**Phase 1 — the self-contained-ish gates (least lookup-entangled).**
1. `ForeignFieldAdd` — limb add + carry + bound; ~4 constraints; the cleanest new gate. Needs a PS
   foreign-field-add gadget or a hand-authored fixture.
2. `Rot64` — the rotation identity; the excess range-check can be left as a separate row.
Deliver: enum + `Checker` + dispatch + `kindOf` + one fixture each, `check = true`, tamper `= false`.

**Phase 2 — the range/XOR gates (row constraints only, lookup gap documented).**
3. `RangeCheck0`, then `RangeCheck1` (its 2-row companion). Reuse RangeCheck0's crumb helpers.
4. `Xor16` — nibble-sum constraints (the XOR itself is the table).

**Phase 3 — `ForeignFieldMul`.** The heavy one (2 rows, ~20 constraints, quotient/remainder limb
arithmetic + carries). Do last; it exercises the most of the checker infrastructure.

**Phase 4 (separate track) — the lookup argument.** Model plookup (sorted table + multiset/
grand-product, or the extensional "every looked-up tuple is in the table" consequence, mirroring how
`copyHolds` models the permutation extensionally). This is what upgrades Phases 1–3 from *checker
coverage* to *algebraic soundness* for the range/XOR/FF gates.

## Depth axis (per gate, after the checker row)

Optional, in the established `Gate/<Gate>.lean` shape: a `Witness` struct, `Holds`/`ok`/`ok_iff`, and
a `sound_*` proving the intended arithmetic against a spec (`ZMod`/limb reconstruction, not the
constraint restated). For the lookup-entangled gates this stays *partial* until Phase 4. `Generic`
and `ForeignFieldAdd` are the ones where full soundness is reachable without lookups.

## The per-gate template (checklist to add one gate, path A)

1. `Kimchi/Circuit.lean`: add `| <gate>` to `GateKind`; add the `rowHolds`/`rowOk` branch dispatching
   to `Checker.<Gate>.holds`/`.ok`; extend `rowOk_iff` and `check_iff`'s `simp` set with the new
   `ok_iff`.
2. `Kimchi/Checker/<Gate>.lean`: transcribe the constraints from `proof-systems/.../<gate>.rs`;
   prove `ok_iff` (the standard `simp only [ok, holds, …, beq_iff_eq, and_assoc]`).
3. `Kimchi/Json.lean`: add the `typ` string to `kindOf`.
4. Fixture: PS gadget (or hand-authored) → `formal/fixtures/<gate>_step.json`; confirm
   `make lean-check-fixtures` accepts it and a tampered copy fails.
5. Register any headline `ok_iff` in `scripts/check_axioms.lean`.
6. (optional) `Gate/<Gate>.lean` algebraic soundness.

## Effort snapshot

- Lean checker per gate: small (mirrors an existing `Checker/*.lean`), ~a day each incl. `check_iff`.
- Fixture per gate: **variable** — free if a PS gadget exists (only `RangeCheck`-ish today),
  otherwise gated on writing a PS gadget or hand-authoring from the Rust backend.
- `ForeignFieldMul`: several days (constraint volume).
- Lookup argument (Phase 4): a project of its own; the gating dependency for real arithmetic-gate
  soundness.
