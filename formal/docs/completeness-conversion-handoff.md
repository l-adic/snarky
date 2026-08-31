# Completeness conversion — handoff

Operational companion to `completeness-framework.md`. That document argues *why* the
primitive set is what it is; this one says what was converted and how, so that future
work on the laws does not rediscover the mechanics.

Branch: `completeness-framework`.

## The goal — ACHIEVED

`Runs` and `Sat` are the prover interpreter's internals. They used to be named in files
all over the tree, because most `_complete` laws were written before the combinators
existed and constructed `⟨a, st', Runs …, Sat …, post⟩` tuples by hand.

**They are now named only in `Snarky/Prover.lean`, where both are `private`** — the
abstraction boundary is enforced by the module system, not by convention. Every gadget
file, the seam (`Witness.lean`, `Compile.lean`), and the schnorr exemplar are at zero
(`grep -o 'Runs' | wc -l` and `grep -o 'Sat\b' | wc -l` per file).

What crossed the flip:

- `witness_complete` and `runs_witness` were **merged into `Complete.witness`**
  (`Witness.lean`), whose proof discharges the run and row obligations without naming
  the internals: the run component via `show prove _ st.nv st.env = _` (the definitions
  unfold by defeq), the rows via a plain `intro con hcon`.
- `solve_complete` (`Compile.lean`) states a combinator law for `compileBody` — check,
  body, output witness and binding rows chained with `bind`/`frame`, the output value
  named by `instantiate` off the body's `WellFormed` post — and then **applies** the
  `Complete` at the seed, destructuring the existential. Destructuring is fine: the
  components' types mention the private names, the source text does not.
- Two public accessors serve proofs that destructure a `Complete` directly:
  `run_le` (the run component's two order facts) and `runs_post` (a soundness spec read
  at the run's own table — used by `Complete.post`, and directly by
  `pow_complete`/`any_complete`/`all_complete`). Neither name contains the internals.
- The API manifests were updated in step: `snarky/roots.txt` and
  `snarky/scripts/check_axioms.lean` list the `Complete` rules instead of the
  `Runs`/`Sat` family and `witness_complete`.

Inside a proof, the goals still *display* the private names after `intro st h` on a
`Complete` — that is expected; what the module system forbids is writing them.

## The rules

All in `Snarky/Prover.lean` except `Complete.witness` (`Snarky/Witness.lean`) and
`Mono.onCurveAs` (`Snarky/Kimchi/Circuit/AddComplete.lean`).

```
interpretation   Complete.pure_of   Complete.addConstraint   Complete.witness
structural       Complete.bind      Complete.imp             Complete.frame
precondition     Complete.of_false  Complete.instantiate
Mono vocabulary  Mono.and  Mono.readsAs  Mono.forall₂  Mono.scoped  Mono.onCurveAs
```

`Complete.seq` still exists and four files still use it, but it is now *derived*
(`bind ∘ imp ∘ frame`). Prefer `bind` + `frame` in new work; `seq` fuses them and forces
`Mono` on the caller.

## The shape of a conversion

Nearly every law is one of four shapes.

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

**A composite.** `bind`, with `frame` wherever the old proof had a `.mono` transport:

```lean
  exact Complete.bind
    (Complete.imp ADAPTER (fun _ _ h => h) (Complete.frame Mono.readsAs (first_complete …)))
    fun r => Complete.imp ADAPTER POST (second_complete …)
```

**A recursion over a `Forall₂` precondition.** The relation is state-dependent, so it
cannot index the recursion; `of_false` discharges the branches the precondition rules
out. See `RandomOracle.foldBlocks_complete`.

**A precondition carrying only scope or well-formedness.** Use `instantiate` to name the
value the law is indexed by. See `Field.powGo_complete` and `Boolean.xor.core_complete`.

**A loop whose invariants pin a state.** `EndoScalar`'s `AccInv`/`CrumbRow` are indexed
by the crumb witness's landing table `st₁`. `instantiate` handles states as well as
values: index over a `ProverState`-subtype whose property carries the pinned cells'
scope and readings, with `P i st := i.1.nv ≤ st.nv ∧ i.1.env.Le st.env`, discharged at
the current state with `⟨st, facts⟩` and two `refl`s. `EndoMul` uses it twice — the
bits' landing table, then the walk's seed coordinates (with the point they name as the
subtype property).

An `addConstraint` row obligation quantifies over `env.Le` extensions only — but
`ProverState.nv_le_of_env_le` (in `Prover.lean`) recovers `nv_le` from the states'
`dom` invariants, so ordinary `.mono` transports still work there (`EndoMul`'s row
case). `EndoScalar` predates the lemma and instead split `RowGrant.holds_of_le` out of
its `mono`; prefer the lemma in new work.

Two elaboration rules of thumb from `EndoMul`: keep every `Complete.imp` post-map the
identity `(fun _ _ h => h)` and extract in the NEXT stage's pre-map (a non-trivial
post-map leaves the bind's `mid` undetermined and anonymous constructors fail to
elaborate); and hoist any pre-map component whose type mentions a constructed bundle
(`⟨phix, t.y⟩`) into a named pointwise `have` before the `refine`.

## Gotchas, all of which cost time at least once

- **`refine` returns its `?_` holes in an unpredictable order.** Four times the
  advice-runs goal and the row goal came out swapped. Check the first error before
  assuming your bullets are wrong, or name the holes.

- **A `split` on a CVar *constructor* renames the theorem's binders.** The goal then
  mentions `t✝¹ e✝¹`, and every explicit argument must be read off the goal. The fix is
  not to fight it: factor the witnessing branch into a `where core` and prove its law in
  its own binders. `xor` already had this shape; `selectField` was given it. No further
  file needed it — `AddComplete`, `VarBaseMul` and `GroupMap` all branch on plain data
  (an enum, a `Bool`, a `Fin`), where `cases`/`by_cases`/`match` at the law level
  suffices. The trick is only for splits on a *CVar* scrutinee.

- **A long straight-line chain is fine without state indexing** when every value is a
  function of the law's own parameters: `GroupMap`'s 26-step chain is 26 `bind`s with
  per-step frames, contexts kept to at most eight conjuncts by dropping each reading at
  its last use. Track the mid-shape per step in a comment margin while writing; the
  projection paths are the whole difficulty.

- **A `Mono` witness whose predicate is itself a `∀` needs its type pinned.** A lambda
  like `fun _ _ hnv hle h x hx => …` is ambiguous while the frame's `R` is a
  metavariable — hoist it into a `have hM : Mono (F := F) fun st => ∀ x ∈ …` first
  (`VarBaseMul`'s `hpinM`). Deeply conjunctive contexts also read better with the base
  `Mono` named once (`scaleRound_complete`'s `hMP`) and per-step wrappers
  `Mono.and Mono.readsAs hMP` inline.

- **The precondition of a framed law is sometimes a conjunction and sometimes curried.**
  `rintro st ⟨hr, hx⟩ stf hle` vs `rintro st hr hx stf hle` — read the goal.

- **`Complete.pure_of` needs its `pre` pinned** when applied at a state
  (`Complete.pure_of (pre := …) … st h`), or the metavariable is stuck.

- **A mid-`do` `if` inlines its continuation into both branches.** After
  `by_cases hc … <;> simp only [hc, if_true]` the true branch's program is
  `g >>= fun _ => (pure ⟨⟩ >>= fun _ => REST)` — the branch body does NOT group as
  `(g >>= pure ⟨⟩) >>= REST`. Factor `REST`'s law as a `have hrest : Complete …` (with
  the merged mid as its pre) and finish each branch with
  `Complete.bind … fun _ => hrest` (`RangeCheck.lowest128Bits'_complete`).

- **Anchor text edits precisely.** `attribute [irreducible] X` occurs more than once in
  some files; slicing to the first occurrence deletes half the module.

## Gate discipline

Match the gates to the change class — see the memory note `ci-gates-are-mine`.

A proof-internal conversion is invisible to most gates. Run:

```sh
lake build Kimchi KimchiFixture Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture Schnorr
./scripts/check-style.sh
lake exe runLinter Snarky        # and Schnorr if that package changed
./scripts/deadcode.sh            # whenever a declaration is added or removed
```

If the change touches a **definition** (as `selectField.core` did), also run:

```sh
cd snarky && lake env lean scripts/check_cs_basic.lean   # constraint systems unchanged
cd snarky && lake env lean scripts/check_axioms.lean
```

Before pushing, run the whole CI Gates list — read it from
`.github/workflows/lean.yml`, not from memory.

## What is not being claimed

`Complete.bind` needs an intermediate assertion. The one that always exists is the
strongest postcondition, and it mentions `Runs` — so now that `Runs` is private, a law
whose value-level postcondition is too weak for its consumer must be *restated*, not
worked around by unfolding. That is the intended trade, and it is why this work makes
interface debt unavoidable rather than absent. `completeness-framework.md` §7 has the
argument.

The rule count is not proven minimal. `of_false` and `instantiate` were both discovered
by conversion, not predicted, at a rate of roughly one per two files. Both were duals of
rules already present, which is weak evidence of convergence — not a guarantee that a
ninth will not appear.
