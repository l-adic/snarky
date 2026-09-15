# Pickles rule DSL and compiler — simplification plan

Plan for re-founding the PureScript pickles "rule construction" layer on
runtime slot data instead of type-level shape machinery, for fixing the
rule/prover interface so that a rule never mentions a proof, and for
slimming the rule-to-circuit translation (`Step/Main`, `Wrap/Main`)
accordingly. The circuits themselves, and their byte-for-byte parity with
the OCaml dumps, are unchanged by design.

## 1. Thesis

The semantics of a pickles application is fixed by the paper's Section 9.2
(`~/code/paper/kimchi-spec.tex`, Definitions tag / rules / application /
family / derivation): a rule is a relation on its public wires

    r ⊢ ({input, output}, (s_i, b_i)_{i<n})  ⟺  ∃ w. Sat_r(w, input, (output, (s_i, b_i)_{i<n}))

and everything a compiler needs to know about a slot i is

    T_i          the tag (statement type S_{T_i}, its max_proofs_verified, and a key or
                 Self / side-loaded)
    enc_{T_i}    the statement's encoding as an F_p vector (Section 9.5 encodes every
                 statement); the compiler uses the encoding, never its length alone

together with `mpv = max_r n_r` over the rules of the application. None of
this is type-level information in OCaml either: `inductive_rule.ml` stores
`prevs : H4.T(Tag).t`, an H-list of runtime `Tag.t` values, and
`step_main.ml` folds over it. The OCaml GADT indices exist to make the
H-list well typed; they carry no data the fold does not also have at
runtime.

The PureScript port transliterated those GADT indices into type classes
with one instance per shape, and the integer bookkeeping (`mpv`, padding,
chunk counts) into type-level naturals reflected back to `Int`. That is the
entire source of the size and opacity of `Pickles/Prove/Compile.purs` and a
good part of `Step/Main.purs`. Replacing it with an `Array Slot` and plain
functions is a refactor of the compiler, not of the protocol.

Two facts about the rule interface are settled by the OCaml history in §10
and are taken as constraints here:

- the dependency statements `s_i` and the bits `b_i` are **outputs** of the
  rule, computed in circuit from its witness (required: PRs #11016, #11018);
- the proofs are matched to slots by the **harness**, after the rule has
  run, and never appear in the rule's type (the OCaml proof handle in
  `main`'s return is a channel artefact, PR #11083, not a requirement).

## 2. Current state (measured 2026-09-13)

| File | Lines | What is in it |
|---|---|---|
| `packages/pickles/src/Pickles/Prove/Compile.purs` | 4193 | types/config (1–460); `CompilableSpec` class + instances (461–2177, one instance is 1512 lines); `CompilableRulesSpec` Nil/Cons (2184–2740); orchestrator (2738–3190); per-rule packaging and prove contexts (3194–4193) |
| `packages/pickles/src/Pickles/Prove/Step.purs` | 2211 | step proving; `StepRule` / `StepRuleAt` rank-2 rule types; shape dispatch mixed in |
| `packages/pickles/src/Pickles/Step/Main.purs` | 1280 | the step circuit; plus `BuildSlotVkSources` (one instance per shape), `IntEq`, `MpvPaddingDispatch`, `Reflectable` indices `n`, `stepChunks`, `mpvPad`, `mpvMax`, `nd` |
| `packages/pickles/src/Pickles/Wrap/Main.purs` + `Wrap/Slots.purs`, `Wrap/SlotsFromSpec.purs` | 951 + | the wrap circuit; type-level spec → slots conversion |

Type-level classes to be removed: `CompilableSpec`, `CompilableRulesSpec`,
`CompilableRulesSpecShape`, `ConvertSlots`, `PadProveDataMpv`, `IntMax`,
`IntMaxOrd`, `MaxOfRulesMpvs`, `RulesSpec`/`RulesCons`/`RulesNil`,
`BuildSlotVkSources`, `IntEq`, `MpvPaddingDispatch`, and the
`SlotsFromSpec` machinery on the wrap side.

Symptom to keep in mind as the yardstick: `compileMulti`'s signature
quantifies over roughly thirty type variables with a dozen `Reflectable`
constraints, to compile a list of rules.

The rule-facing interface is *already* the paper's and already proof-free:

    type RuleOutput n prevInput output =
      { prevPublicInputs :: Vector n prevInput            -- s_i, outputs
      , proofMustVerify  :: Vector n (BoolVar StepField)  -- b_i, outputs
      , publicOutput     :: output }

and the proof channel is already harness-side: proofs are supplied to the
prover call as `prevs`, one `InductivePrev proof tag` per slot, and the
harness reads `prevs[i]` positionally. In the example's `mergeRule` the
rule obtains `s_i` by `exists` from advice the harness populated from
`prevs[i]`'s statement, then returns it; the harness and the rule agree
because both used `prevs[i]`. This interface is kept in Phases 1–3 so
application code does not churn; §3.4 generalises the proof channel.

## 3. Target design

### 3.1 Runtime slot data

Shape fixed by the Phase 0 inventory
(`pickles-rule-dsl-phase0-inventory.md`, §6.1 and §7):

    type Slot =
      { tag              :: SomeTag            -- existential over the phantom statement type;
                                               --   packs the statement's CircuitType dictionary
      , localMpv         :: Int                -- the slot's own max_proofs_verified (the tag's n);
                                               --   every per-slot width on the wrap side, and
                                               --   mina #19235's mask width max 2 localMpv
      , kind             :: Self | External CompiledTagData | SideLoaded
      , sourceDomainLog2s :: Array Int         -- step-domain log2 per branch of the slot's source;
                                               --   replaces the uniform type-level `nd`
      }

    -- OCaml Types_map.Compiled (types_map.ml:12–21, 100–112): the constants a
    -- compiled tag contributes, all baked into the circuit.  A wrap VK alone is
    -- not enough: the step circuit also bakes in the prev's domains and zk_rows
    -- (Compile.purs 799–837).
    type CompiledTagData =
      { wrapVk          :: WrapVk
      , wrapDomainLog2  :: Int
      , stepDomainLog2s :: Array Int
      , numChunks       :: Int                 -- zkRows derived
      }

    type RuleSpec =
      { name   :: String
      , slots  :: Array Slot
      , main   :: StepRuleAt …          -- unchanged rank-2 rule type, n now a runtime Int
      }

    type AppSpec = { rules :: Array RuleSpec }         -- mpv = maximum (map (length <<< _.slots) rules)

There is no `stmtSize` field: nothing in the compiler reads a statement's
length (inventory OQ-5). What it needs is the statement's `CircuitType`
dictionary, carried by `SomeTag`, and the statement *values* (dummy or
real), which arrive with `prevs` at the prove call.

The side-loaded bound is `localMpv`, the same field as for the other two
kinds, which settles §8 question 2 in favour of the tag.

`Tag stmt mpv` keeps its phantom `stmt` at the API so that `mergeRule`'s
signature stays typed and `InductivePrev proof tag` still refuses a proof
of the wrong statement type. Erasure to `Vector F_p` happens once, at the
prove call, through the existing `CircuitType` instance; that is where
Section 9.5 says it happens.

### 3.2 The compiler

The three `CompilableSpec` methods become three functions over `Array Slot`:

| Today (per-shape instance) | Target (one function) |
|---|---|
| `shapeCompileData` | `slotCompileData :: Int (mpv) -> Array Slot -> CompileData` — per-slot VK source (const / advice / side-loaded), dummy slots to pad to mpv |
| `mkStepAdvice` | `mkStepAdvice :: Array Slot -> Array Prev -> StepAdvice` — per-slot prev statement / proof / must-verify into the advice record |
| `shapeProveData` | `slotProveData :: Array Slot -> Array Prev -> ProveData` — messages-for-next-wrap, unfinalized proofs, per-slot wrap domain |

`CompilableRulesSpec` becomes a `traverse` over `rules`. `MaxOfRulesMpvs`
becomes `maximum`. `PadProveDataMpv` becomes `padTo mpv dummySlot`. The
orchestrator (pre-pass then real pass per branch, then wrap) is kept as
is; it already operates on values.

Validation that the types used to give for free moves to explicit checks
at compile time, returned as errors exactly where OCaml raises: a prev
count not equal to the rule's slot count, a prev whose statement type is
not the slot's (the `SomeTag` unpack), a side-loaded key whose `mpv`
exceeds the slot's `localMpv`, a slot width or count above the protocol
cap (today 2; `Compare n 3 LT` at Prove/Step 538, Wrap/Main 418).

Two type-level indices survive the runtime compiler, and **§9 concludes
both should keep surviving**.

`outputSize = 32·mpv + 1 + mpv` is the step circuit's return type
`Vector outputSize` and the `Proxy` handed to `compile` / `makeSolver'`
(Step/Main 858–870, Prove/Step 1754, 1957, 2103). This is not a pickles
decision to make: `compile` takes the circuit's public output as a
`Proxy` and counts its field elements through `CircuitType`, so the width
has to be in the type. Neither option this paragraph used to offer — an
existential over `outputSize`, or a runtime-length output — is available
without changing `snarky`, which the reified-`Typ` work deliberately did
not do. See §9.2; open question 3 is closed.

The width a slot's *consumers* use — the one in `verifyOne`,
`finalizeOtherProofCircuit` and `challengePolyEvals` — is a second
residue this section did not name. It is unconstrained in all three
signatures, and erasing it would be a downgrade. See §9.2.

### 3.3 The translation layer

`Step/Main.purs` keeps its circuit body untouched: per slot, `ivp` on the
previous wrap proof gated by the must-verify bit, the message hashes, the
unfinalized-proof fields, the statement assembly. What changes is only how
the slot list reaches it:

- `BuildSlotVkSources` and its per-shape instances → a `map` over
  `Array Slot` producing the per-slot VK source.
- `MpvPaddingDispatch` / `IntEq` → `replicate (mpv - length slots) dummy`.
- `Reflectable n / stepChunks / mpvPad / mpvMax / nd` → plain `Int`
  arguments.

`Wrap/Main.purs` likewise: `SlotsFromSpec` → the same `Array Slot`, and the
per-branch selection over `branches` becomes a loop over a runtime count.

Vectors indexed by type-level naturals may remain *inside* the circuit
code where they encode fixed protocol widths (`Vector 32` of unfinalized
fields, `Vector 15` of columns, chunk counts); those are protocol
constants, not application shape. The rule is: a length that varies per
application (`n`, branch count) is runtime; a length fixed by kimchi or
pickles stays in the type; and a length that is neither stays in the type
only for a reason stated at the site.

`mpv` is the third case. It varies per application *and* is named by the
specification, so the two-way split above has no room for it. §9.3.

Chunk counts (`stepChunks`, `wrapVkChunks`) are explicitly out of scope
for Phases 1–3. They vary per application but index protocol records
inside the circuit (`Vector stepChunks` in `IncrementallyVerifyProof`,
`PublicInputCommit`), not the slot list; leave them as they are.

The per-slot chunk count is load-bearing in a way this section
underestimated: it also indexes the carriers the compiler's methods
*return*, which is what keeps `CompilableSpec` alive through Phase 3.
§9.1.

### 3.4 The rule / prover interface, and the proof channel

The interface the DSL exposes, per rule r with slots T_0 … T_{n−1}:

    rule_r  : Input_T × witness → Snarky (Output_T × Π_{i<n} (S_{T_i} × Bool))
              -- what the author writes.  s_i and b_i are OUTPUTS.  No proof anywhere.

    prove_r : Input_T × witness × Π_{i<n} (S_{T_i} → Proof_{T_i}) → (s, Q)
              -- what the harness exposes.  The i-th function is the caller's;
              -- the harness calls it AFTER rule_r has run, on the s_i it produced.

Today's `InductivePrev proof tag` is the special case `const proof`; a
caller holding several candidate proofs supplies a lookup keyed by the
statement's field encoding or hash.

**Why statements are outputs and not inputs.** A rule that merely knows
its dependency statements from outside (the merge rule) witnesses them
from advice and returns them; a rule that *determines* them from its own
witness (the blockchain snark hashing the previous protocol state; the
transaction snark building the zkApp statement from the party it is
processing) computes them in circuit and returns them. If statements were
inputs, the second kind of rule would have to reconcile the harness's
value with its own by an equality assertion, and the caller would have to
run a copy of the rule's logic outside the circuit to produce the input.
OCaml had exactly that until May 2022 and removed it (§10). The two kinds
differ only inside the box; the interface is the same.

**Bits.** `Required` dependencies compile to the constant `true` and drop
out of the box's return; `Optional` ones are returned by the box, as the
blockchain snark's `¬is_base_case` and `ledger changed` are. Sugar over
the interface above, no compiler change.

**Mechanics at proving time.** Snarky generates the witness in one pass in
program order, and the harness's per-slot code follows the rule's:

    (output, (s_i, b_i)_i) ← rule_r input                       -- rule's constraints and witness
    for each i:
      q_i ← exists (proverValue) ~compute (lookup_i (read s_i))  -- no variables; the proof object, prover-only
      w_i ← exists PerProofWitness.typ ~compute (partsOf q_i)    -- commitments, evaluations, deferred values, challenges
      verify_slot_i (s_i, b_i, w_i)                               -- ivp gated by b_i, against s_i

Because `rule_r` has already run when the harness's `exists` executes,
`read s_i` is a concrete value and `lookup_i` sees it. A proof whose public
input is not `s_i` simply fails `verify_slot_i` and the prover errors. This
is the "delay prev-proof processing until the circuit has started running"
of OCaml PR #11014, with the fetch placed in the harness instead of at the
end of `main`.

### 3.5 Other interpreters of the same data

Once `AppSpec` is runtime data it has more than one interpreter, and the
compiler is only one of them. None of the others should read circuits.

**Evaluation (run without proving).** `rule_r` is a `Snarky` program;
snarky can run it on concrete values and check every constraint without a
prover, as the test utilities do today. So

    eval_r : Input_T × witness → Either ConstraintFailure (Output_T × Π_i (S_{T_i} × Bool))

and a derivation is built by evaluating rules and, for every true bit,
recursively requiring a derivation of that slot's statement. This is
Definition derivation executed: application tests run in milliseconds with
no prover; a failing constraint reports its `with_label` path; a recorded
derivation is a proving plan the prover replays later, so "simulate, then
prove exactly what was simulated" is one workflow (`packages/example`'s
`Simulation` does this by hand today). Property tests over rules follow
for free. Depends only on runtime `AppSpec` and runnable rules, not on the
compiler refactor.

**Family graph.** Definition family of the paper, drawn out:

    nodes:  resolved tags T
    edges:  one per slot, (T, branch ℓ, slot i) → T_i, labelled Self | External | SideLoaded

Nodes carry ports typed by `Input_T` / `Output_T`; edges carry the slot's
statement type `S_{T_i}`. This is Figure 9(a) of the paper.

**Derivation graph.** At prove (or eval) time, one node per invocation
`(rule, statement)` and one edge per dependency consumed, pointing at the
invocation that produced it. Definition derivation, Figure 9(b); sharing
is visible when one proof feeds two nodes.

**Declared data flow.** Which ports a rule equates is declared at the
interface, not recovered from the circuit:

    flow_r : Array (Port, Port)
    -- merge: [ (input.source, s_1.source), (s_1.target, s_2.source), (s_2.target, input.target) ]

The compiler emits the `assertEq` for every declared pair, so the
declaration *is* the constraint; the graph interpreter draws the pairs as
port-to-port edges. Whatever the rule does beyond declared flow stays
inside the box. Recovering flow by reading copy constraints out of the
compiled circuit is explicitly rejected: it couples the graph to the
compiler's output and reports accidents of compilation as design.

**Target representation.** A plain record, serialized as JSON, with
printers over it:

    type Graph = { nodes :: Array { id, label, kind, ports }
                 , edges :: Array { from, to, branch, slot, kind } ∪ { flow :: (Port, Port) } }

Printers: DOT (Graphviz, for looking), Mermaid (renders inline on GitHub,
for docs), TikZ in the style of the paper's Figure 9 so the family and
derivation figures are generated rather than hand-drawn (`~/code/paper/figs`
already generates figures from scripts). Both graph interpreters produce
the same `Graph`, so the printers serve both.

## 4. Correctness gates

Every phase must leave these green, with **identical circuit digests**
before and after:

1. `packages/pickles-circuit-diffs` — constraint-system JSON comparison
   against the OCaml dumps (see `.claude/skills/kimchi-circuit-json-comparison`).
2. `packages/pickles/test/Test/Pickles/Prove/*` — the shapes that exercise
   every slot kind: `NoRecursionReturn` (0 slots), `SimpleChain` and
   `SimpleChainN2` (Self, 1 and 2 slots), `TreeProofReturn` (External),
   `SideLoadedMain` (side-loaded), `TwoPhaseChain`, `Chunks2`, `Chunks4`
   (chunk counts), `CompileValidation` (the error paths of §3.2).
3. `packages/pickles/test/Test/Pickles/Sideload/*` — side-loaded VK round
   trips and NRR digests.
4. `packages/example` — the transaction application (`baseRule` with 0
   slots, `mergeRule` with 2 Self slots) end to end through
   `Snarky/Example/Prover.purs`.
5. The Lean side reads recorded circuits and proofs, not PureScript
   source; if digests are identical nothing there moves. Confirm by
   re-running the fixture regeneration (`tools/regen_chunks_fixtures.sh`)
   and diffing.

Digest identity is the whole test: the circuits are supposed to be
bit-for-bit what they were, since only their construction changes.

## 5. Phases

### Phase 0 — inventory (no code) — DONE 2026-09-14

Recorded in `pickles-rule-dsl-phase0-inventory.md`: every class method and
`Reflectable` index in `Prove/Compile`, `Prove/Step`, `Step/Main`,
`Wrap/Main`, `Wrap/Slots`, `Wrap/SlotsFromSpec`, classified runtime /
type / derived, with line numbers. Outcome: the `Slot` of §3.1 above
(three fields added, `stmtSize` removed); `outputSize` is the one
type-level residue (§3.2); chunk counts stay type-level as planned
(inventory OQ-8, OQ-11); 11 housekeeping items (inventory §6.4) are not
blockers.

MinaProtocol/mina PR #19235 ("Add support for wider recursion", merged
2026-09-14) raises the cap on previous proofs from 2 to 6 while keeping
every width-2 encoding and circuit unchanged, so no digest here moves.
Every new quantity is an integer function of `localMpv` and `mpv`
(mask width `max 2 localMpv`, `prev_challenges = max 2 mpv`, wrap domain
2..6 → 15). The five PS sites that hard-code the cap are listed in
inventory §5; none moves in Phases 1–3. The `mina` submodule
(f2265df310) predates the PR.

### Phase 1 — runtime compiler behind the existing API — SUPERSEDED, see §9.1

As written: introduce `Slot`, `RuleSpec`, `AppSpec`, and the three
functions of §3.2; implement `compileMulti` as an adapter over them.

**This is not buildable.** The three methods can take an `Array Slot`;
they cannot return one. Each returns a carrier indexed per slot by that
slot's own chunk count, and no function over an array can build a
per-slot type-indexed chain. §9.1.

**What was done instead** (`worktree-pickles-rule-dsl-phase1`): the
runtime `Slot` type was introduced and every per-slot derivation moved
behind it, and the three methods' duplicated instance bodies were
collapsed to one shared body each. `Prove/Compile.purs` 4193 → 3751.
Commits `c320838a`, `9ac3ea92`, `bfe19d41`. Gates green, digests
identical.

### Phase 1b — evaluation interpreter — NEXT, and never was blocked

`eval_r` and the derivation checker of §3.5, over the Phase 1 `AppSpec`.
Port one existing prove-based test (the SimpleChain chain) to evaluate the
chain and prove once from the recorded derivation. Exit: the evaluated
chain and the proved chain agree on every statement; wall-clock of the
evaluated test is reported.

### Phase 2 — runtime translation layer

Route `Array Slot` into `Step/Main` and `Wrap/Main`; remove
`BuildSlotVkSources`, `MpvPaddingDispatch`, `IntEq`, `SlotsFromSpec`, and
the application-shape `Reflectable` indices. Exit: gates green, digests
identical.

### Phase 3 — delete the shape machinery — BLOCKED as written, see §9.1

Remove `CompilableSpec`, `CompilableRulesSpec`, `CompilableRulesSpecShape`,
`ConvertSlots`, `PadProveDataMpv`, `IntMax*`, `MaxOfRulesMpvs`, `RulesSpec`
and their instances. Replace `compileMulti`'s signature with one over
`AppSpec`.

`ConvertSlots` and the `SlotsFromSpec` machinery are gone. The rest is
blocked behind the per-slot chunk count for the reason in §9.1, and that
axis should stay. Rewrite this phase around what survives, or scope the
chunk axis as its own project first — it is larger than everything on the
branch so far, because that count sizes the in-circuit inner-product base
layout and not merely a container.

The padding classes are the exception and are *not* blocked:
`MpvPaddingDispatch`, `IntEq` and `MpvPadding` pad vectors that are
homogeneous in their element type and sized only by the rule's slot
count, so the reified-`Typ` technique that erased the step witness width
applies to them directly. That is the one piece of this phase available
today.

### Phase 4 — optional: black-box sugar, proof lookup, graph interpreters, paper alignment

Add the `Required`/`Optional` dependency sugar and the `flow_r` declaration
of §3.4 / §3.5; generalise `prevs` from positional `InductivePrev` to the
per-slot lookup `S_{T_i} → Proof_{T_i}` of §3.4 (positional stays as the
`const` case); add the family and derivation graph interpreters with the
DOT, Mermaid, and TikZ printers. Add to the paper's Section 9.2 the
one-line translation from the black-box form to Definition rules, and the
completeness statement (a derivation over framework rules yields a proof by
invoking `prove_r` along it), which the paper currently lacks.

## 6. Estimates

Measured by the Phase 0 inventory (machinery = class declarations,
instances, constraint blocks, in-body dispatch and `unsafeCoerce`
bridges; body = circuit code and value-level proving logic that does not
change).

| Module | Now | Shape machinery | Untouched body | After |
|---|---|---|---|---|
| `Prove/Compile.purs` | 4193 | classes 461–531, 544–2115, 2137–3182 ≈ 2700 | orchestrator + packaging 2749–4193 ≈ 1450 | ≈ 1000–1300 |
| `Prove/Step.purs` | 2211 | ≈ 300 (three runner signatures ≈ 216) | ≈ 1100 | ≈ 1900 |
| `Step/Main.purs` | 1280 | ≈ 370 | ≈ 710 | ≈ 950 |
| `Wrap/Main.purs` + `Slots` + `SlotsFromSpec` | 951 + 197 + 39 | ≈ 572 | ≈ 475 | ≈ 650 |

The runtime replacements are not free: the three slot functions of §3.2
and the explicit validation take space that the instances did not.

## 7. Risks

Checked non-blockers: feature flags (the port emits eight constant zeros,
no per-rule flags exist; if added they are runtime booleans per rule);
proof widths (already hidden behind `SomeCompiledProofWidthData` in
`Verify.purs` / `SerializeProof.purs`, the same existential move); Self vs
External detection (already runtime via `Tag`'s `Unique`); the proof
channel (harness-side already, §2; the lookup generalisation of §3.4 is
additive).

- **Lost compile-time length checks.** Slot counts and statement sizes are
  no longer in types. Mitigation: the explicit validation of §3.2 at
  compile time, and the digest gates, which check the actual circuit and
  so are stronger than the types were.
- **Rank-2 rule types and advice monads.** `StepRule` / `StepRuleAt` and
  the `AsProver … r valCarrier` threading are orthogonal to shape and are
  kept; the doc comment on `StepRuleAt` explains why the runner is pinned
  to a concrete `m`. Do not touch in Phases 1–3.
- **Performance.** None: identical circuits, identical proving; the
  compiler does less work, not more.
- **Parity drift by accident.** Any digest change is a failure of the
  phase, not something to be "fixed" in the fixtures. The fixtures are
  the OCaml's.

## 8. Open questions

1. Whether `RuleOutput` should keep `Vector n` for the rule author or
   move to `Array` with a runtime length check. Keeping `Vector n` costs
   nothing at the API and preserves the current examples verbatim;
   recommended for Phases 1–3.
2. The key of the proof lookup when a caller holds several candidates:
   the statement's field encoding, or its hash. Encoding is exact;
   hashing is what the wire already carries. Decide in Phase 4.
3. ~~`outputSize` (§3.2): existential at the three `compile` /
   `makeSolver'` sites, or a runtime-length output type.~~ **Closed**:
   neither is available without changing `snarky`. §9.2.
4. `slotVkChunks` is documented as the prev's *step* chunk count
   (`Pickles/Slots.purs:39–50`) and used as the slot's *wrap-VK* chunk
   count (`Compile.purs` 736, 1447, 1538–1540), unified with
   `wrapVkChunks` in `BuildSlotVkSources`' heads (inventory OQ-8). Both
   are 1 in every fixture. Pick one name and meaning; the value stays
   type-level. Note this is now known to be the axis that keeps
   `CompilableSpec` alive (§9.1), so the naming matters more than it did
   when the value looked incidental.

Resolved (see §10): statements are outputs, not inputs, of the rule; the
proof channel is harness-side and the rule's type never mentions proofs.
Resolved (Phase 0): the side-loaded `mpv` bound is the tag's `localMpv`,
the same field every kind carries (§3.1).
Resolved (§9.4): the wrap domain is one value per compile, not per slot,
and no estimator exists on either side.

## 9. Findings from implementing this plan (2026-09-15)

Checked on `worktree-pickles-rule-dsl-phase1`, base `origin/main`. Each
item corrects or adds to the section it names.

### 9.1 Phases 1 and 3 are not buildable as written (§5)

§5 has the three `CompilableSpec` methods become functions over
`Array Slot`, and Phase 3 then delete the class. Their *inputs* can be an
array. Their *outputs* cannot: each returns a carrier indexed per slot by
that slot's chunk count — the VK blueprint chain and the per-proof
witness carrier. A function over an array cannot build a per-slot
type-indexed chain, so the class survives and Phase 3 sits behind it.

This is not a defect in the chunk axis. A slot verifies a proof from
another application; applications are compiled independently; an
application importing one chunked tag and one unchunked one has slots
that genuinely differ in it. That every slot declaration in the
repository says `1` is a fact about the fixtures, not the axis. §3.3 and
open question 4 are right to keep it type-level.

What landed instead is the deduplication half: each method's two
near-verbatim instance bodies became one shared body, with the instances
supplying only what differs. 1254 deletions against 856 insertions.

Reifying the chunk axis, if ever wanted, is much harder than the slot
widths were. A width only sized containers, so an array plus a width
sufficed. The chunk count also determines how many bases the in-circuit
verifier folds, through a chain of multiplications and additions, so
erasing it changes loop structure inside the circuit.

### 9.2 Two residues that should stay type-level (§3.2)

`outputSize` cannot be erased here. `compile` takes the circuit's public
output as a `Proxy` and counts its field elements through `CircuitType`.
Making it runtime is a `snarky` change, which the reified-`Typ` work
deliberately avoided. Open question 3 closes as "not a pickles decision".

The consumer-side slot width — in `verifyOne`,
`finalizeOtherProofCircuit` and `challengePolyEvals` — is unconstrained
in all three signatures. No reflection, no arithmetic. Its only effect is
to tie the mask, the challenge stacks and the opening points to one
length, which is what keeps five zips total. Erasing it would trade those
for silently truncating array zips inside the sponge digest and the
inner-product helpers, where a truncated mask absorbs fewer challenges.
**No gate here could catch that**, because every fixture builds the three
collections from a single width, so they always agree. Leave it.

### 9.3 §3.3's rule has no room for `mpv`

A length varying per application is runtime; a length fixed by kimchi or
pickles stays in the type. `mpv` is neither: it varies per application
*and* is named by the specification. §3.3 now carries a third case.

### 9.4 The wrap domain was computed three ways, all wrong

The compiler derived it from the three-entry table in three places:
applied to the number of slots from that position to the end of the list,
and applied to the head slot's own bound. An override then replaced the
result, which is why nothing failed — every rule is either single-slot,
where the readings coincide, or overridden, where none is consulted.

OCaml computes one value per compile: the override when given, otherwise
the table applied to `max_proofs_verified`. That is now what this does
(`31a467aa`).

**There is no estimator on either side.** `Wrap_domains.Make.f`, the
function `compile.ml:472` calls, is only the table lookup. The same
functor defines `f_debug`, which builds a dummy wrap circuit and measures
it, but nothing calls it, and the file carries a TODO asking why the
functor ignores its own arguments. The table is a guess in both
languages; the override is how a wrong guess is corrected.

OCaml also checks the guess against the wrap circuit it built and fails
naming both sizes. That check had no port; it does now (`4fdbd087`).
Without it a wrong guess surfaced much later as a kimchi permutation
error naming neither the domain nor the override.

### 9.5 A two-slot rule with no override cannot work, in either language

Consequence of §9.4, recorded because it looks like a test gap. The
table says 15 for two proofs; `SimpleChainN2`'s wrap circuit is really
14. Removing its override makes the new check fire with exactly those two
numbers. OCaml hits the same wall, which is why its own dumper passes
`override_wrap_domain`. There is no such fixture to write, and the
positional reading corrected in §9.4 had never worked.

### 9.6 The incremental type-check gives false greens (§4)

`check` returned clean in 0.2 s on a tree whose build had five real
errors, more than once. Only the gates of §4 are evidence for anything
crossing a module boundary, and they must run sequentially: they drive
`spago` against the same build directory.

For work like §9.1 the prove gate is the load-bearing one. Those bodies
do cross-field coercions and oracle calls that only end-to-end proving
exercises, so a bad text move passes a type-check and fails there.

## 10. History: why OCaml's rule mentions proofs, and what was actually required

Six PRs by mrmr1993, May–June 2022, one project: #11008 → #11014 →
#11016 → #11018 → #11083 → #11282/#11319. Stated goal (#11282, closing
issue #10968): "allow us to construct a `Parties.t` within a circuit,
instead of needing to precompute it". All reviewed and approved by
imeckler.

**Before (2020 – May 2022).**

    (* inductive_rule.ml *)
    { prevs      : ('prev_vars, 'prev_values, 'widths, 'heights) H4.T(Tag).t
    ; main       : 'prev_vars H1.T(Id).t -> 'a_var -> 'prev_vars H1.T(E01(B)).t
                   (* prev statements IN, input, one Boolean.var per slot OUT *)
    ; main_value : 'prev_values H1.T(Id).t -> 'a_value -> 'prev_vars H1.T(E01(Bool)).t
                   (* the same function, unchecked, run by the prover before the circuit *) }

    (* pickles.mli *)
    Prover.t = ?handler -> ('prev_values, 'widths, 'heights) H3.T(Statement_with_proof).t
                         -> 'a_value -> 'proof
    Statement_with_proof.t = 's * ('w, 'w) Proof.t      (* caller supplies (s_i, Q_i) per slot, positionally *)

The harness needed every `s_i` and `b_i` before running the circuit:
`s_i` to allocate the variables it handed to `main`, `b_i` to know which
previous proofs needed witnesses. So the caller supplied `s_i`
positionally and `main_value` recomputed `b_i` outside.

**Why it had to change.** In the transaction snark `s_i` and `b_i` are
functions of the witness: a segment folds over the transaction's parties,
and the party with `auth_type = Proof`, if any, determines the previous
statement `{party = hash; calls = at_party}` and the bit. Under the
interface above the caller ran that fold outside the circuit
(`zkapp_statements_of_forest'`), threaded the results positionally
(`snapp_statements`, with `assert (List.is_empty snapp_statements)` to
check the bookkeeping), and the circuit reconciled the two copies with

    Zkapp_statement.Checked.Assert.equal { party = party.hash; calls = at_party } s

one per proof-authorised party: duplicated logic outside the circuit, plus
constraints whose only purpose was the interface. `main_value` was the
same duplication for the bits.

**After (#11016, #11018).**

    { prevs : … H4.T(Tag).t
    ; main  : 'a_var -> 'prev_vars H1.T(Previous_proof_statement).t }      (* input IN; (s_i, b_i) OUT *)
    Previous_proof_statement.t = { public_input : 'prev_var; proof_must_verify : B.t }

The circuit computes `s_i` where it knows it (`set_zkapp_input {party;
calls}`); the harness reads `s_i` and `b_i` out of the circuit run with
`As_prover.read`. The outside fold, the positional threading, the equality
assertion and `main_value` are deleted. This is the necessary change:
**outputs, not inputs, for data the witness determines.** imeckler's
review of #11016 (removing `main_value`): "Wow! Cool".

**After (#11083).**

    Previous_proof_statement.t = { public_input : 'prev_var
                                 ; proof : ('w, 'w) Proof.t As_prover.Ref.t   (* prover-only handle *)
                                 ; proof_must_verify : B.t }
    Prover.t = ?handler -> 'a_value -> 'proof                                 (* positional proof list gone *)

`main` obtains each proof by request and returns it; the harness takes
proofs from `main`'s return instead of from `prove`'s argument. Stated
motive: "delays the need for previous proofs until the end of the pickles
circuit's main logic, allowing the public outputs to depend on as-yet-
uncomputed proofs and their public inputs/outputs."

**How #11083 could have been done otherwise, and what it did not deliver.**
`main` cannot use the proof: its type has no circuit representation, and
every use of it is in `step_main.ml`'s per-slot fold after `main` returns.
The harness could therefore ask the caller for slot i's proof *after*
running `main`, with `s_i` in hand:

    prev_proof_i : S_{T_i} → Proof            (* supplied to prove; consulted after main returns *)

Same laziness, no proof in the rule's type. Evidence it suffices: after
#11083 the SnarkyJS handler answers `Get_prev_proof i` from the caller's
positional `prevs` array, and the transaction snark's `handle_zkapp_proof
p` is constructed with `p` before the circuit runs. The requests carry an
index or nothing, never `s_i`, so the landed design does not select or
produce a proof from the rule's outcome either; the part that depends on
the circuit's run, *which statement*, was already delivered by #11018.
#11083 bought a uniform channel (requests from inside the circuit are
OCaml pickles' only channel for prover-only data) and a cleaner `prove`
signature, and the rule's return type paid for it.

**Net.** Required: statements and bits as rule outputs. Not required: the
proof handle in the rule. A proof-free DSL is §3.4's `rule_r`, with proofs
matched to slots by the harness after the rule runs. The PureScript port
already has this shape; the plan keeps it and generalises the match from
positional to a lookup.

## References

- Paper: `~/code/paper/kimchi-spec.tex`, Section 9.2 (rules, applications,
  derivations), 9.4 (the harness), 9.5 (encodings at the boundary).
- OCaml: `mina/_build/default/src/lib/crypto/pickles/inductive_rule.ml`
  (the rule record), `step_main.ml` (the fold over `rule.prevs`, `verify_one
  … must_verify`), `compile.ml`.
- Production dynamic bits:
  `mina/src/lib/blockchain_snark/blockchain_snark_state.ml:348-383`.
- OCaml history (MinaProtocol/mina PRs): #11008 step statement as output;
  #11014 delay prev-proof processing; #11016 remove `main_value`; #11018
  statements from circuit logic; #11083 proofs from circuit logic; #11282
  return values; #11319 auxiliary values. Issue #10968.
  Commits: 085a66cf50 (#11018), 5a07c04324 (#11083), 1874045d0b (#11319).
- PureScript proof channel today: `packages/pickles/src/Pickles/Prove/Compile.purs`
  (`PrevSlot`: `BasePrev` / `InductivePrev`), `packages/example/src/Snarky/Example/Transaction/Checked.purs`
  (`mergeRule`, `mergeProver`).
- Prior plans in this directory: `pickles-compile-prover-api-plan.md`,
  `step-wrap-prover-port-plan.md`, `sideload-vk-module-refactor.md`.
