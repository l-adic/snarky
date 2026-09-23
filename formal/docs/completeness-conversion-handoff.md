# Completeness laws in the snarky package — a working guide

How to state and prove a gadget's `_complete` law with the `Complete` combinators, and
how the `complete_walk` tactic mechanizes the straight-line case.

`Runs` and `Sat`, the prover interpreter's internals, are `private` in
`Snarky/Prover.lean`; no other file can name them. Every law is built from the rules
below. Inside a proof, goals still display the private names after `intro st h` on a
`Complete`; only writing them is forbidden. Two public accessors serve proofs that
destructure a `Complete` directly: `run_le` (the run component's two order facts) and
`runs_post` (a soundness spec read at the run's own table, used by `Complete.post` and by
`pow_complete`/`any_complete`/`all_complete`). `solve_complete` (`Snarky/Compile.lean`)
shows the seam pattern: state a combinator law for `compileBody`, then apply it at the
seed and destructure the existential. `snarky/roots.txt` and
`snarky/scripts/check_axioms.lean` list the rules.

## The rules

All in `Snarky/Prover.lean` except `Complete.witness` (`Snarky/Witness.lean`) and
`Mono.onCurveAs` (`Snarky/Kimchi/Circuit/AddComplete.lean`).

```
interpretation   Complete.pure_of   Complete.addConstraint   Complete.witness
structural       Complete.bind      Complete.imp             Complete.frame
precondition     Complete.of_false  Complete.instantiate
Mono vocabulary  Mono.and  Mono.readsAs  Mono.forall₂  Mono.scoped  Mono.onCurveAs
```

`Complete.seq` is derived (`bind ∘ imp ∘ frame`). Prefer `bind` + `frame` in new work;
`seq` fuses them and forces `Mono` on the caller.

## The shape of a conversion

Nearly every law is one of these shapes.

**A leaf that emits a row.** Frame the operands' readings across the allocation, because
the row needs them and the witness rule does not carry them:

```lean
  simp only [gadget]
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
        (Complete.witness (gadget.advice x y) VALUE (by simp))))
    (fun r => Complete.bind (Complete.addConstraint ?_)
      fun _ => Complete.pure_of fun _ h => h.1)
  · -- the advice runs at the entry table
    simp [gadget.advice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1), …]
  · -- the row holds at every extension
    rintro st ⟨hr, hx, hy⟩ stf hle
    refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
    rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hx.1), …]
```

**A composite.** `bind`, with `frame` wherever a reading must survive the head's run:

```lean
  exact Complete.bind
    (Complete.imp ADAPTER (fun _ _ h => h) (Complete.frame Mono.readsAs (first_complete …)))
    fun r => Complete.imp ADAPTER POST (second_complete …)
```

**A recursion over a `Forall₂` precondition.** The relation is state-dependent, so it
cannot index the recursion; `of_false` discharges the branches the precondition rules
out. See `foldBlocks_complete` (`Snarky/Kimchi/Circuit/RandomOracle.lean`).

**A precondition carrying only scope or well-formedness.** Use `instantiate` to name the
value the law is indexed by. See `powGo_complete` (`Snarky/DSL/Field.lean`) and
`xor.core_complete` (`Snarky/DSL/Boolean.lean`).

**A loop whose invariants pin a state.** `EndoScalar`'s `AccInv`/`CrumbRow` are indexed
by the crumb witness's landing table `st₁`. `instantiate` handles states as well as
values: index over a `ProverState`-subtype whose property carries the pinned cells'
scope and readings, with `P i st := i.1.nv ≤ st.nv ∧ i.1.env.Le st.env`, discharged at
the current state with `⟨st, facts⟩` and two `refl`s. `EndoMul` uses it twice — the
bits' landing table, then the walk's seed coordinates (with the point they name as the
subtype property).

An `addConstraint` row obligation quantifies over `env.Le` extensions only, but
`ProverState.nv_le_of_env_le` (in `Prover.lean`) recovers `nv_le` from the states'
`dom` invariants, so ordinary `.mono` transports still work there (`EndoMul`'s row
case). `EndoScalar` instead splits `RowGrant.holds_of_le` out of its `mono`; prefer the
lemma in new work.

Two elaboration rules of thumb from `EndoMul`: keep every `Complete.imp` post-map the
identity `(fun _ _ h => h)` and extract in the next stage's pre-map (a non-trivial
post-map leaves the bind's `mid` undetermined and anonymous constructors fail to
elaborate); and hoist any pre-map component whose type mentions a constructed bundle
(`⟨phix, t.y⟩`) into a named pointwise `have` before the `refine`.

## Gotchas

- `refine` returns its `?_` holes in an unpredictable order; the advice-runs goal and
  the row goal often come out swapped. Check the first error before assuming the
  bullets are wrong, or name the holes.

- A `split` on a CVar constructor renames the theorem's binders. The goal then
  mentions `t✝¹ e✝¹`, and every explicit argument must be read off the goal. Factor the
  witnessing branch into a `where core` and prove its law in its own binders, as
  `xor.core` and `selectField.core` do. Branches on plain data (an enum, a `Bool`, a
  `Fin`), as in `AddComplete`, `VarBaseMul` and `GroupMap`, need only
  `cases`/`by_cases`/`match` at the law level.

- A long straight-line chain needs no state indexing when every value is a function of
  the law's own parameters. Keep contexts small by dropping each reading at its last
  use, and track the mid-shape per step while writing; the projection paths are the
  whole difficulty.

- A `Mono` witness whose predicate is itself a `∀` needs its type pinned. A lambda like
  `fun _ _ hnv hle h x hx => …` is ambiguous while the frame's `R` is a metavariable —
  hoist it into a `have hM : Mono (F := F) fun st => ∀ x ∈ …` first (`VarBaseMul`'s
  `hpinM`). Deeply conjunctive contexts read better with the base `Mono` named once
  (`scaleRound_complete`'s `hMP`) and per-step wrappers `Mono.and Mono.readsAs hMP`
  inline.

- The precondition of a framed law is sometimes a conjunction and sometimes curried:
  `rintro st ⟨hr, hx⟩ stf hle` vs `rintro st hr hx stf hle`. Read the goal.

- `Complete.pure_of` needs its `pre` pinned when applied at a state
  (`Complete.pure_of (pre := …) … st h`), or the metavariable is stuck.

- A mid-`do` `if` inlines its continuation into both branches. After
  `by_cases hc … <;> simp only [hc, if_true]` the true branch's program is
  `g >>= fun _ => (pure ⟨⟩ >>= fun _ => REST)`, not `(g >>= pure ⟨⟩) >>= REST`. Factor
  `REST`'s law as a `have hrest : Complete …` (with the merged mid as its pre) and finish
  each branch with `Complete.bind … fun _ => hrest` (`lowest128Bits'_complete`,
  `Snarky/Kimchi/Circuit/RangeCheck.lean`).

- `attribute [irreducible] X` occurs more than once in some files; anchor text edits
  precisely.

## The walker

`Snarky/Tactic.lean` mechanizes the straight-line shape: `complete_walk` walks a
`Complete pre (g₁ >>= …) post` goal bind by bind, at each step selecting the gadget's
`@[complete_law]`, synthesizing the frame's `Mono` witness from `@[complete_mono]`
(both label attributes, `Snarky/Tactic/Attr.lean`; downstream files extend the tables
by tagging), and discharging the adapter by search, which pins the law's witness values
by unification, so laws carry no value arguments. It absorbs `assumption`-shaped side
conditions and defers the rest as end-of-proof VCs. It stops at `pure` or at a bind
with no registered law, main goal kept first, each step atomic.

`groupMapCircuit_complete` (`Snarky/Kimchi/Circuit/GroupMap.lean`) is the exemplar:
`simp only [groupMapCircuit]; complete_walk`, then `simp [potentialXs]`-provable
raw↔spec identities, the value-case blocks, and the VC discharges. The walker pins the
raw compositional value at every step; when a consumer needs a folded spec form, state
the identification once as a `have` and rewrite it in, rather than threading it through
the chain.

Walker internals:

- `refine` cannot defer a step's mid (it insists on synthesizing the dependent
  implicits); `apply` postpones, and named holes solved in dependency order — law,
  adapter, continuation — make elision work. `case'` (not `case`) lets a step's value
  goals and deferred side conditions rejoin the goal list.
- Searches run at reducible transparency, or the `ReadsAs`-family abbreviations unfold
  to `∧` and the search explodes. Depth limits must exceed the context size: the
  defaults (6) silently strand goals once the context outgrows them.
- Law order is most-specific-first (reverse registration): a composite law's program can
  share a prefix with a primitive law's (`ySquared_complete` starts with `mul`), and the
  composite must win.
- Quotation hygiene: attribute names in macro quotations need `mkIdent`; each kernel
  invocation needs `withFreshMacroScope` or its named holes collide; multiline tactic
  sequences do not parse inside quotations — build single tactics and splice.
- Goal types can be `mdata`-wrapped (`cleanupAnnotations` before `getAppFn`), and
  `partial def`s are opaque to the dead-code pass — root their callees alongside them.

Out of scope by design: loops, state-indexed invariants, `instantiate`-shaped
preconditions. Those proofs stay on the combinators.

## Gates

A proof-internal change is invisible to most gates. Run, from `formal/`:

```sh
lake build Kimchi KimchiFixture Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture Pickles
./scripts/check-style.sh
lake exe runLinter Snarky
./scripts/deadcode.sh            # whenever a declaration is added or removed
```

A change to a definition also needs:

```sh
lake exe check-cs                              # constraint systems unchanged
cd snarky && lake env lean scripts/check_axioms.lean
```

The full list is the CI Gates job in `.github/workflows/lean.yml`.

## Interface debt

`Complete.bind` needs an intermediate assertion `mid`. The one that always exists is the
strongest postcondition, and it mentions `Runs`, so it cannot be written outside
`Prover.lean`. Each gadget law instead supplies a value-level postcondition phrased in
`ReadsAs` / `OnCurveAs`, and nothing guarantees it is strong enough for a given consumer.
A law whose postcondition is too weak must be restated, not worked around by unfolding.
The `Mono` vocabulary (`Mono.readsAs`, `Mono.onCurveAs`, `Mono.forall₂`, `Mono.const`)
and the per-proof reading adapters are this debt: each is a postcondition shape or a
bridge between two shapes. The remedy is stating each law at the type its gadget
operates on.

The rule set is not proven minimal; `of_false` and `instantiate` are duals of other
rules, and a further dual may yet be needed.
