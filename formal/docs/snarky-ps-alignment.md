# Snarky package — aligning the Lean port with the PureScript original

**Status: PROPOSED — nothing below is executed.** Companion to `CLAUDE.md`'s package table
(which describes the *current* layout) and to `kimchi-reorg.md` (the precedent for this kind of
move-then-fill reorganization). When this plan is enacted, this banner becomes the migration
record, kimchi-reorg style.

**Scope: the core `snarky` package only** — `packages/snarky` is the original,
`formal/snarky` the port. Nothing in this plan concerns `packages/snarky-kimchi` (the Plonk
backend, gate reduction, wiring) or a Lean analogue of it; the existing `Snarky/Kimchi/*`
bridge modules are left untouched and are otherwise outside this plan. Where the core PS
package *defines a seam* whose only consumers live in snarky-kimchi (the
`CompileCircuit`/`SolveCircuit` backend classes), the seam is noted and deliberately not
ported — see D5.

## 0. Goal and constraints

**Goal.** Re-found `formal/snarky` on the module layout and API surface of its PureScript
original (`packages/snarky`), so that (a) a reader can navigate the Lean port with the `.purs`
tree as the map, (b) the DSL gadget layer — today almost entirely unported — has a designated
place to grow, gadget-for-gadget against the original, and (c) the port covers the original's
*whole* pipeline: `Backend/Compile.purs` (public-input allocation, the solver) is part of the
core package, and its absence is the biggest functional gap in the port.

**What "follows the layout" does NOT mean.** The PS package is final-tagless
(`Snarky f c r a = CircuitOps f c r -> Effect a` — uninspectable), so none of the interpreter
laws are statable against it. The Lean deep embedding (`CircuitM`, one constructor per
`CircuitOps` field) is the reason the laws can exist and is **kept exactly as is**. The laws
live BESIDE their subjects (interpreter laws in `Backend/{Builder,Prover}`, gadget laws
beside their gadgets — D3/D12; the dedicated `Laws.lean` was dissolved at step 10b).
Alignment is about the module tree, the API names, and coverage — not the embedding style.

**Invariants through every step:**

- The five audited roots (`build_eraseWitness`, `prove_assignments_le`, `prove_build_agrees`,
  `prove_complete`, `CVar.eval_le`) stay green under `scripts/check_axioms.sh` — standard axioms
  only — at every sign-off boundary (§5).
- Standard-library discipline: **no reimplementing core-Lean or Mathlib basics** to avoid an
  import. Where a module needs algebraic structure it takes Mathlib's classes (`Field`,
  `CommSemiring`, …) via targeted imports (D6); each module keeps the weakest classes its
  content needs. The first targeted import (`Mathlib.Algebra.Ring.Defs`, for the
  affine-reduction theorem) arrives already at walk step 1, and the `CLAUDE.md` snarky
  paragraph (currently "Mathlib-free by design") is updated in the same step.
- Examples validate by `decide` where practical (concrete `ZMod p` instantiations reduce
  fine — `Snarky/Kimchi/Example.lean` already does exactly this); executable paths keep
  avoiding well-founded recursion so kernel reduction works.
- No axioms, no `sorry`, no `native_decide` — unchanged discipline.

**Authorship context.** The `.lean` sources are kejace's four landing commits (2026-07-10..13,
untouched since). The port's kernel — `CVar`/`eval_le`, `CircuitM`, `build`/`prove`, the laws —
is sound and carries over; the divergence from the original is coverage and layout, not a
competing design. This plan migrates that kernel rather than rewriting it.

## 1. Where the port stands — divergence audit

Module-by-module against the PS tree (PS ~3.2k LOC over 17 modules; Lean 1.2k over 15):

| PureScript module | Lean today | status |
| --- | --- | --- |
| `Circuit/CVar` | `Snarky/CVar.lean` | partial — `CVar` + `eval` + `eval_le`; no folding smart constructors (`add_`, `scale_`, …), no `AffineExpression`/`reduceToAffineExpression`; `Assignments` and `EvalError` folded in |
| `Circuit/Types` | `Snarky/Types.lean` | partial — `CircuitType`/`CheckedType` with `Vector F size` (an improvement over PS's `Array f` + runtime size contract); only `F` and `Bool` instances; no generic/record deriving |
| `Constraint/Basic` | `Snarky/Constraint/{Basic,R1CS}.lean` | diverged — PS: concrete `Basic f = R1CS \| Equal \| Square \| Boolean` **plus** a 4-method `BasicSystem` class. Lean: a 2-method class (no `equal`, no `square`) and a bare `R1CS` type |
| `Circuit/DSL/Monad` | `Snarky/{Monad,AsProver}.lean` | present (deep embedding — the sanctioned deviation); advice row `r` dropped (deliberate); `labelOp` inert in both interpreters |
| `Circuit/DSL/Field` | — | missing (`equals_`, `neq_`, `sum_`, `pow_`, `square_`) |
| `Circuit/DSL/Boolean` | — | missing (`IfThenElse`/`if_`, `xor_`, `any_`, `all_`) |
| `Circuit/DSL/Assert` | `assertEq` in `Snarky/DSL.lean` | missing but for one combinator (no `assertNonZero_`, `assertSquare_`, `assertAny_`/`All_`/`ExactlyOne_`, `allBools`, `AssertEqual` class) |
| `Circuit/DSL/Bits` | — | missing (`unpack_`/`pack_` + pure variants) |
| `Circuit/DSL/SizedF` | — | missing (stretch; needs Bits + a bit-width bound) |
| `Circuit/DSL/Utils` | — | missing (`seal`) |
| `Circuit/DSL` (barrel) | `Snarky/DSL.lean` | partial — 4 combinators (`witness`, `readVar`, `mul`, `assertEq`), no numeric-tower instances |
| `Backend/Builder` | `Snarky/Builder.lean` | present (pure recursion in place of `Effect`/`Ref` — correct translation); the `CompileCircuit` seam it also hosts in PS is not ported (D5) |
| `Backend/Prover` | `Snarky/Prover.lean` | present; `holds` as a *parameter* replaces the PS `SolveCircuit` class (keeps `c` abstract — keep, see D5) |
| `Backend/Compile` | — | **missing** — no public input/output allocation, no `compile`/`makeSolver`; `build` stops at `List c` |
| `Backend/Assignments` | inside `Snarky/CVar.lean` | present as `Nat → Option F` + `Le` + guarded `extendPairs` (stronger than PS — keep) |
| `Backend/Advice` | — | dropped, deliberately (stays dropped) |
| `Circuit/EvalError` | — | not a module in the Lean port: PS defines the error *type* in `Circuit/CVar.purs` (`EvalError.purs` is only the JS-exception transport, replaced structurally by `Except`), so `EvalError` stays in `Circuit/CVar.lean` |
| — | `Snarky/Laws.lean` | Lean-only payload (5 theorems) — no PS analogue possible |

(`Snarky/Kimchi/{Backend,Example}.lean` exist in the tree; they are outside this plan's scope
and untouched by the migration apart from the stale-comment fixes below.)

Known rot, fixed for free by the migration's doc pass:

- Three doc comments cite a theorem that does not exist under that name —
  `Snarky.Laws.build_eq_of_sameShape` at `Snarky/AsProver.lean:19`, `Snarky/Builder.lean:41`,
  `Snarky/Monad.lean:16`; the actual name is `build_eq_of_eraseWitness`.
- `Snarky/Kimchi/Backend.lean:27` and `:113` cite declarations that exist nowhere
  (`Snarky.Kimchi.Compile`, `Snarky.Kimchi.satisfies_of_prove`) — described as if adjacent.
  Rewrite both comments as plain statements of what the module does *not* cover; whatever
  becomes of that bridge is outside this plan.
- `roots.txt` records the dead-code deferral: 76 authored `Snarky.*` declarations, 43
  unreachable from the 8 roots — the unreachable set *is* the DSL API. The gadget ports below
  shrink this measurably (each gadget lands with `decide` examples and, where meaningful, laws
  that become roots).

## 2. Decisions

**D1 — layout mirrors PS; embedding does not.** The deep `CircuitM` stays. File paths mirror
the `.purs` tree so the original is the map; the Lean-only theorems (the reason the port
exists) claim no extra module — they live beside their subjects (D3).

**D2 — namespaces stay flat; paths move.** Declarations today live in flat `Snarky.*`
(`Snarky.build`, `Snarky.prove_complete`) with dot-namespaces only from type names
(`Snarky.CVar.eval_le`). The relocation keeps every declaration name byte-identical, so
`roots.txt` and `scripts/check_axioms.lean` are untouched by the move (kimchi-reorg precedent:
its gate split also kept the namespace fixed). The kimchi package's "namespace matches path"
convention is *not* imported here; for a 20-file package, `Snarky.*` is unambiguous and
name-stability is worth more.

**D3 — proofs live beside definitions, with no exceptions** (revised at step 10b; the
original clause parked interpreter-spanning theorems in a dedicated `Laws.lean`, since
dissolved). Per-module lemmas sit with their definitions, kimchi house style; the
interpreter laws sit beside the interpreters (`build_eraseWitness`, `build_bind` in
`Backend/Builder`; `prove_assignments_le`, `prove_build_agrees`, `prove_complete`,
`prove_bind`, `prove_witnessCore` in `Backend/Prover`); gadget laws sit beside their
gadgets — for which the gadget modules import the backend, a deliberate deviation from the
PS import graph (adjacency over layering). One cycle forces one displacement: the
interpreters import `Circuit/DSL/Monad`, so its gadgets' laws (`mul`/`inv`/`div`,
`and`/`or`) live with their gadget families (`DSL/Field`, `DSL/Boolean`).

**D4 — `Constraint/Basic` is refounded on the PS shape.** Concrete
`inductive Basic F | r1cs | equal | square | boolean` with `holds : Basic F → Assignments F →
Bool` and `holds_mono`, plus `BasicSystem` widened to the four PS methods (`r1cs`, `equal`,
`square`, `boolean`). Every gadget is written against `BasicSystem`, never against `Basic` —
exactly the PS discipline. `Constraint/R1CS.lean` is subsumed and deleted; its two roots are
replaced by `Basic.holds`/`Basic.holds_mono` in the same PR.

**D5 — the backend-seam classes are not ported.** PS `CompileCircuit` (in `Backend/Builder`)
and `SolveCircuit` (in `Backend/Prover`) exist so a backend can substitute its own constraint
type and gate reduction; their only real instances live in snarky-kimchi, which is out of
scope. The Lean port's abstraction point stays what it is today: the `BasicSystem` class on
the emission side and the `holds` parameter on the checking side. The class machinery pays
for itself only when a second backend arrives, and that is explicitly not this plan.

**D6 — standard algebra comes from Mathlib; nothing homegrown.** Gadgets that need field
structure (`equals_` and `assertNonZero_` need an inverse) take the weakest fitting Mathlib
class — `[Field F] [DecidableEq F]` in practice — via *targeted* imports, the same
targeted-import discipline the workspace's executable trees already use. We do not introduce
bespoke stand-ins (`HasInv`-style classes) for things core Lean or Mathlib already provide,
and we do not rewrite core implementations to dodge an import. Consequence, accepted: the
package is not Mathlib-free — the first targeted import lands with `Circuit/CVar`'s
reduction theorem (walk step 1), `DSL/Field` adds `Field` (step 9); what matters is fast
builds (targeted imports) and `decide`-friendly examples (`ZMod p`), both preserved.

**D7 — PS names port without the trailing underscore; renames are recorded.** The PS `_`
convention separates var-level ops from lifted ones — a distinction the Lean port doesn't
have (no numeric-tower instances, see D8). So: `mul_` → `mul`, `equals_` → `equals`,
`assertEqual_` → `assertEq` (already so), `if_` → `select` (decided at step 10: `if` is a Lean
keyword; the class keeps its PS name `IfThenElse`), `exists` → `witness` (Lean keyword, already
renamed), `true_`/`false_` keep their underscores (keyword clash), `not_`/`and_`/`or_`/`xor_`/
`any_`/`all_` drop them, shadowing core's Bool functions inside the namespace (type-directed
resolution disambiguates). Each gadget file's docstring carries its PS→Lean name map.

**D8 — deliberate non-ports stay non-ported, now documented in place.** The advice row
(`Backend/Advice`), `MonadRec`, the numeric-tower instances on `Snarky`-actions, and the
generic/rowlist deriving machinery (`GCircuitType`/`RCircuitType`, `GCheckedType`/…) are out
of scope. Each gets one line in the module docstring of the file where PS defines it, so the
gap is visible where a reader will look for it. (Deriving may return later as a `deriving`
handler; nothing in this plan blocks it.)

**D9 — PS QuickCheck properties become theorems, surveyed at every step.** The PS test
suite reaches for QuickCheck wherever possible — `packages/snarky/test` plus the
backend-parameterized suite in `packages/snarky-test-utils` — so each walk step includes a
deliberate survey of the QuickCheck properties touching its module, and every assertion
that states a law is ported as a theorem (private per D10 unless it is one of the module's
named top-level results). This is a strict upgrade: a QuickCheck run samples the property,
the theorem closes it. E.g. the Constraint-spec property "`CVar.eval` agrees with
`evalAffineExpression ∘ reduceToAffineExpression`" is now `CVar.reduce_eval`. Fixed-input
specs (round-trip tables, edge cases like `2^128 − 1`) land as `decide` examples instead;
a property that resists proof at reasonable cost is recorded in the module docstring as an
open obligation rather than silently dropped.

**D10 — private by default.** Only the port surface (the PS export list, def for def) and
each module's named top-level theorems are public; every supporting lemma and helper
definition is `private`, and each module's docstring names its public results. Top-level
results so far: `CVar.reduce_eval` (`Circuit/CVar`); `Assignments.Le` (+ `refl`/`trans`),
`le_extendPairs`, and `CVar.eval_le` (`Backend/Assignments`). Roots must be public (the
axiom gate resolves them by name). A lemma is promoted from private only when a
cross-module consumer appears.

**D11 — phantom type tags become nominal wrappers with private constructors.** Where PS
draws a type-level distinction with a phantom tag on the variable-index parameter
(`BoolVar f = CVar f (Bool Variable)`; later `SizedF`), the Lean port uses a nominal
structure wrapping the expression, with a PRIVATE constructor. PS itself has three
introduction mechanisms: `exists` at the tagged type (pays `check`), `exists` at
`UnChecked _` (the typed opt-out — how `xor_` witnesses its result), and ambient
`Safe.Coerce` (how `equals_` retags its record-witnessed `r`; `Bool(..)` is exported, so
retagging is available anywhere). The Lean rendering keeps the first two verbatim through
`witness`, and replaces the third by ONE explicit function, `BoolVar.unchecked`, reserved
for pure retaggings (a negation, a constant answer) with each call site owing a
booleanity argument — strictly narrower than PS's ambient coercibility. Elimination
(forgetting the tag) is free — a `Coe` instance, so `↑b` — matching PS's eliminating
coerces; only introduction is guarded, and deliberately NOT a coercion, since the
elaborator inserts `↑` silently on type mismatches.
(`CircuitType.fieldsToVar` remains a public class method that builds the wrapper —
`witness` factors through it — but it is implementation surface, not a gadget door; PS's
`Bool` instance is itself a `coerce`.) Settled at walk step 9, against `equals_`/`xor_`.

**D12 — gadget laws are stated against the interpreters, never re-derived over the
field.** A gadget's law must mention the gadget: soundness quantifies over every
assignment satisfying the constraints `build` emits — adversarial witnesses included —
and pins the result's evaluation; completeness runs the honest `prove` from any
fresh-enough assignment. Field-identity reformulations that never reference the circuit
are proof engines, kept private — they connect to nothing and would survive gadget
drift. Each law reads off a definitional shape lemma of the built circuit. The laws are
field-generic and live in `Snarky/Laws.lean` (the gadget modules mirror the PS layering,
below the backend, so interpreter theorems cannot live beside them — D3's
interpreter-spanning clause). Stated over the reference `Basic` backend; transport to
other backends (a lawful-`BasicSystem` class with per-constructor `holds` equations)
arrives with its first non-reference consumer. This is the form that composes toward the
arc this package ultimately serves — see
`formal/docs/circuit-verifier-faithfulness.md` and §6. Settled at walk step 9, first
instance `equals_sound`/`equals_complete`.

## 3. Target layout

Relocations (no semantic change; each lands at its §5 walk step):

| new file | from | contents |
| --- | --- | --- |
| `Snarky/Circuit/CVar.lean` | `Snarky/CVar.lean` | `Variable`, `EvalError`, `CVar`, `eval` (PS keeps `EvaluationError` in `CVar.purs` too; the transport-only `EvalError.purs` is not ported, so no `Circuit/EvalError.lean` exists) |
| `Snarky/Backend/Assignments.lean` | `Snarky/CVar.lean` (assignment part) | `Assignments`, `Le`, `extend*`, the `Le`/`eval_le` lemmas |
| `Snarky/Circuit/Types.lean` | `Snarky/Types.lean` | `CircuitType`, `FVar`, `BoolVar` + instances. `CheckedType` moves to `DSL/Monad` — its PS home — flipping today's `Types → Monad` import to the PS direction (`Monad → Types`) |
| `Snarky/Circuit/DSL/Monad.lean` | `Snarky/Monad.lean` + `Snarky/AsProver.lean` | `AsProver`, `CircuitM`, smart constructors, `LawfulMonad`; plus `CheckedType` (from `Types.lean`) and the core combinators `witness`/`readVar`/`mul` (from `DSL.lean`) — all defined in `DSL/Monad.purs` in PS |
| `Snarky/Constraint/Basic.lean` | `Snarky/Constraint/Basic.lean` | (refounded at walk step 3, see D4) |
| `Snarky/Backend/Builder.lean` | `Snarky/Builder.lean` | `allocRange`, `Built`, `build`, `constraints` |
| `Snarky/Backend/Prover.lean` | `Snarky/Prover.lean` | `Proved`, `prove` |
| `Snarky/Circuit/DSL.lean` | `Snarky/DSL.lean` | ends as the pure re-export barrel: its combinators disperse to their PS homes (`witness`/`readVar`/`mul` → `DSL/Monad`, `assertEq` → `DSL/Assert`) over the walk |
| `Snarky/Laws.lean` | — | dissolved (step 10b): interpreter laws beside the interpreters, gadget laws beside the gadgets |
| `Snarky/Vec.lean` | `Snarky/Vec.lean` | unchanged |
| `Snarky/Example.lean` | `Snarky/Example.lean` | unchanged (grows per-gadget examples later) |
| `Snarky/Kimchi/*` | `Snarky/Kimchi/*` | untouched (out of scope; stale-comment fixes only) |

New files (each at its §5 walk step):

| new file | mirrors | contents |
| --- | --- | --- |
| `Snarky/Constraint/Basic.lean` | `Constraint/Basic.purs` | concrete `Basic F` (4 cases) + `holds` + `holds_mono`; `BasicSystem` with 4 methods |
| `Snarky/Circuit/CVar.lean` (additions) | `Circuit/CVar.purs` | folding smart constructors; `AffineExpression`, `reduceToAffineExpression`, `reduce_eval` |
| `Snarky/Circuit/DSL/Field.lean` | `DSL/Field.purs` | `equals`, `neq`, `sum`, `pow`, `square`; first module with a targeted Mathlib `Field` import (D6) |
| `Snarky/Circuit/DSL/Boolean.lean` | `DSL/Boolean.purs` | `IfThenElse` class + base `select`, `xor`, `any`, `all` |
| `Snarky/Circuit/DSL/Assert.lean` | `DSL/Assert.purs` | `assertNonZero`, `assertNotEqual`, `assertSquare`, `assertAny`/`All`/`ExactlyOne`, `allBools` |
| `Snarky/Circuit/DSL/Bits.lean` | `DSL/Bits.purs` | `unpack` (n booleans + one weighted-sum constraint), `pack`, pure variants |
| `Snarky/Backend/Compile.lean` | `Backend/Compile.purs` | public input/output allocation, `compile`, `makeSolver`-analogue, end-to-end statement |

`DSL/SizedF` and `DSL/Utils` (`seal`) are follow-ons (§6), not part of the plan's core scope.

## 4. The genuinely new piece — `Backend/Compile`

Everything else is relocation or gadget-for-gadget porting; `Compile` is design work. The PS
original allocates `sizeInFields a + sizeInFields b` public variables up front, runs
`check avar`, the circuit, then asserts each output field against its preallocated output var;
the solver runs the same sequence against live assignments and back-fills the outputs via
`assignVars` before the assert loop, so builder and prover allocate identically. The Lean port
gets this almost for free from the shared `allocRange` discipline:

- `compile (main : avar → CircuitM F c bvar) : Built c …` — allocate public vars from 0,
  emit `CheckedType.check`, run, `assertEq` outputs; all at the DSL level (`build` keeps
  producing `List c` — no gate reduction, per D5).
- `solve` — the same sequence through `prove`, seeded with the input's `valueToFields` image;
  outputs back-filled with `assignOp` (its first real consumer — today nothing uses it; the
  `extendPairs` guard is satisfied because the output slots are allocated-but-unassigned until
  exactly this point).
- The payoff theorem, extending `prove_complete` to the pipeline: a successful `solve` yields an
  assignment satisfying every compiled constraint *and* agreeing with the declared public
  input/output encoding — the end-to-end analogue of `prove_complete`, stated once for the whole
  compile/solve pair.

## 5. Execution order — the module-by-module sign-off walk

The port proceeds one module at a time, each step ending with an explicit sign-off before the
next begins. The order is a topological sort of the *target* tree's imports — which is also
the PS package's layer order — and it puts the inherited kernel (steps 1–8) ahead of the new
gadget layer (9–14): the existing code gets vetted module-by-module against its `.purs`
original before anything new lands on top.

Per step: bring the module to its §3 target state (relocate / split / refound / create),
review it side-by-side with the PS original, record deviations in the module docstring
(D7/D8), survey the PS test suite for QuickCheck properties touching the module and port
each law-stating assertion as a theorem (D9), keep proof machinery private and name the
public results in the docstring (D10), tick the box. Every step leaves the gates green (`scripts/check_axioms.sh`,
`lake lint`, shake, style); one step = one commit or PR. Steps 1–2 are the `CVar.lean`
two-way split and may land as a single commit if separating them is awkward, with two
separate sign-offs on the resulting files.

- [x] 1. `Snarky/Circuit/CVar.lean` — relocate + gap-fill (folding smart constructors,
  `AffineExpression`, `reduceToAffineExpression`, `reduce_eval` per D9). `EvalError` stays
  here (its PS home: `EvaluationError` is defined in `CVar.purs`; the transport-only
  `EvalError.purs` is not ported). First targeted Mathlib import
  (`Mathlib.Algebra.Ring.Defs`, for the reduction theorem) + the `CLAUDE.md` "Mathlib-free"
  wording update. `eval` keeps taking a lookup function (`Variable → Option F`), mirroring
  PS — so this file does not depend on `Backend/Assignments`.
- [x] 2. `Snarky/Backend/Assignments.lean` — split out: `Assignments`, `Le`, `extend*`, the
  `Le`/`eval_le` lemmas (declaration names unchanged, D2).
- [x] 3. `Snarky/Constraint/Basic.lean` — the D4 refound: concrete `Basic F` + 4-method
  `BasicSystem`; `Example.lean` ported off `R1CS`; `Constraint/R1CS.lean` deleted; the two
  R1CS roots swapped for `Basic.holds`/`holds_mono`.
- [x] 4. `Snarky/Circuit/Types.lean` — relocate, minus `CheckedType` (moves to step 5, its
  PS home); missing deriving machinery documented per D8.
- [x] 5. `Snarky/Circuit/DSL/Monad.lean` — merge `Monad.lean` + `AsProver.lean`; absorb
  `CheckedType` and `witness`/`readVar`/`mul` (their PS home is `DSL/Monad.purs`); document
  the deep-embedding deviation, the dropped advice row, and the single scoped `labelOp`;
  fix the three stale `build_eq_of_sameShape` cites.
- [x] 6. `Snarky/Backend/Builder.lean` — relocate; note the un-ported `CompileCircuit` seam
  (D5).
- [x] 7. `Snarky/Backend/Prover.lean` — relocate; document the `holds`-parameter deviation
  (D5) and the emission-time-checking restriction (§6).
- [x] 8. `Snarky/Laws.lean` — no relocation; content review of the five theorems and their
  root entries.
- [x] 9. `Snarky/Circuit/DSL/Field.lean` — new; targeted Mathlib `Field` import (D6).
- [x] 9b. (inserted) The interpreter-composition layer and the gadget-law backfill:
  `build_bind`/`prove_bind` (the bind laws), `Assignments.FreshFrom` (carried per-gadget —
  `assignOp` forbids a general preservation theorem), and D12 laws for every landed gadget
  (`mul`/`inv`/`square` directly; `div`/`pow` compositionally through the bind laws) — the
  lemma library of `formal/docs/circuit-verifier-faithfulness.md`.
- [x] 10. `Snarky/Circuit/DSL/Boolean.lean` — new; `not`/`and`/`or` in `DSL/Monad` (their
  PS home); D12 laws for all of them plus `neq` (a step-9b gap) — `xor`/`select` with the
  full shape-lemma treatment, `and`/`or`/`neq` composed; the `any`/`all` three-plus-case
  laws are the step's recorded obligation (they need a characteristic-bound hypothesis).
- [x] 10b. (inserted) Laws beside their subjects: `Laws.lean` dissolved — interpreter laws
  to `Backend/{Builder,Prover}`, gadget laws beside their gadgets (D1/D3/D12 revised),
  `Basic.r1cs_inv` beside `Basic.holds`, the `bit` lemmas beside `bit`; plus
  `prove_witnessCore`, the generic one-variable honest-run lemma that collapses each
  such gadget's run lemma to its two facts.
- [x] 11. `Snarky/Circuit/DSL/Assert.lean` — new; `assertEq` migrates from the barrel as the
  `AssertEqual` class method (`FVar` call sites unchanged), switching to the `equal` row with
  PS constant folding; PS's construction-time crashes on impossible constant assertions
  become unsatisfiable rows (documented deviation); D12 laws in-file for
  `assertEqual`/`assertNonZero`/`assertNotEqual`/`assertSquare`/`assert`; the sum-based
  `assertAny`/`All`/`ExactlyOne` and `allBools` laws join the characteristic obligation;
  `Basic.{equal,square}_inv` land beside `Basic.holds`.
- [x] 12. `Snarky/Circuit/DSL/Bits.lean` — new; `unpack` (n CHECKED bit witnesses + one
  weighted-sum row), `pack`, the pure variants; `Snarky.ToNat` (the one `PrimeField`
  fragment the bit gadgets need — faithfulness and width are law-side hypotheses,
  discharged at `ZMod` by `ZMod.val`); `generateVec` (kernel-reducible monadic vector
  builder, `DSL/Monad`) and `Basic.boolean_inv` land as prerequisites. The boundary
  engines proved: `packPure_unpackPure` (the round trip), `pack_eval`, `unpack_sound`
  (bits boolean + weighted sum, canonicity joining the characteristic obligation),
  `unpack_complete` (the honest binary digits).
- [x] 13. `Snarky/Circuit/DSL.lean` — the barrel review: every name on PS's export list
  audited to exactly one disposition (ported / D7-renamed / D8-non-ported / §6-deferred —
  no stragglers found), the consolidated PS → Lean surface map written into the barrel's
  docstring, and the two barrel-semantics deviations recorded (import-as-export exposes
  whole module surfaces where PS curates — PS omits `allBools` and the `square` method
  from its list; the backend rides in transitively for the laws).
- [x] 14. `Snarky/Backend/Compile.lean` — the §4 design work + end-to-end example and payoff
  theorem; new roots. Landed: `compile`/`solve` (PS `compile`/`makeSolver`+`runSolver`)
  over ONE shared `compileBody` — PS spells two near-identical programs, but the builder
  ignores `assignOp`, so a single op tree serves both interpreters and the laws quantify
  over it directly. Public slots are canonical (inputs `0..`, outputs `A.size..`);
  `assignVars` gains its first real consumer (the output back-fill assigns into the fresh
  region, the very move that blocks a general freshness-preservation theorem). The payoff
  `solve_complete`: a successful solve satisfies every compiled constraint AND decodes the
  input/output slots as declared — proved by `prove_complete` + bind-decomposition of the
  run, with `readVar_le` (new, beside `readVar`) carrying the mid-run output read to the
  final assignment. End-to-end `cubeCircuit` examples in `Example.lean` (compiled
  constraint list, solved output, slot decodes, failing-assertion rejection). Non-ported
  (D8): `compile'`/`makeSolver'` debug machinery, the advice row, the `Checker` type.
  Post-step amendment (user-directed): `Example.lean` reserved for the showcase — the
  knowledge-of-a-cube-root statement at `ZMod 13` (`PUnit` output, so the root stays
  private; `solve` accepts exactly the cubes, decided exhaustively over the field),
  landing the PS `Unit` `CircuitType` instance with this first consumer; the per-gadget
  D9 checks moved to `Example/Gadgets.lean`.
- [ ] 15. Wrap-up — `Snarky.lean` root imports + orientation docstring; `Vec.lean` and
  `Example.lean` final state; `roots.txt` grown per gadget (retiring the 43-declaration
  dead-code deferral note); the two phantom forward-reference fixes in
  `Snarky/Kimchi/Backend.lean`; the `CLAUDE.md` package-table paragraph.

Each gadget step (9–12) lands with its PS→Lean name map (D7), theorems for the QuickCheck
laws in its `snarky-test-utils` spec plus `decide` examples for the fixed-vector cases
(D9), and correctness lemmas where they are cheap.

## 6. Out of scope — recorded follow-ons

- **The circuit-verifier faithfulness arc** — the long-range goal past this plan: prove
  circuit implementations of the kimchi verifier faithful to the wire-protocol verifier.
  Architecture agreed and recorded in `formal/docs/circuit-verifier-faithfulness.md`:
  per-fragment lemma towers over the D12 gadget laws (the verifier SPLITS by native
  field arithmetic, deferred-values style), the deployed `Kimchi.Verifier` run functions
  as specs, a boundary-encoding library (step 12's Bits round-trips are its engine), and
  a glue theorem with a boundary-consistency hypothesis. Step 14's compile/solve payoff
  statement is the fragment-interface seam. Standing discipline from step 10 on: witness
  code calls the wire functions themselves, keeping the completeness direction
  quasi-definitional.
- **Anything snarky-kimchi-shaped** — a second backend, gate reduction, wiring, or growing
  the `Snarky/Kimchi/*` bridge. Not planned here; see the scope banner and D5.
- **`DSL/SizedF`** — needs Bits plus a `FieldSizeInBits` analogue (a per-field bit-width
  bound; likely a class with a `Nat` and a proof obligation used by `CheckedType`).
- **`DSL/Utils.seal`** — trivial once Assert lands; omitted from the core scope only because
  nothing here consumes it yet.
- **Generic deriving** for `CircuitType`/`CheckedType` (D8), the advice row, numeric-tower
  instances — see D8 for the rationale and the in-place documentation contract.
- **`labelOp` semantics** — today inert in both interpreters. When error attribution is
  wanted, `prove` should thread a label stack into `EvalError.custom` context (PS
  `contextualize`); until then the constructor stays, documented as inert.
- **Emission-time constraint checking** — `prove` rejects constraints over not-yet-assigned
  variables, so circuits must witness before constraining. Document as a known restriction in
  `Prover.lean` now; lifting it (deferred checks at `solve` time) is a design change to take
  up only if a ported gadget actually hits it.
