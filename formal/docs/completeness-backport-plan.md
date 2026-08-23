# Completeness backport plan — the course's prover machinery into `formal/snarky`

Source of truth: the course `martyall/wp`, `main` after PR #1 (`aa8792f` … `6b68f69`). The
course built and measured, on a five-gadget toy, the formulation of completeness that
this plan carries into the codebase. File and line references are at `sound-native`
(`1ffa348e`), which stacks on PRs #313 and #314; the backport starts after those land,
and keeps the soundness half `sound-native` introduced (`Builder V`, `SoundCheckedType`,
`witness_spec`) untouched. Every step names the course commit it inherits from and the
codebase files it touches. Steps are ordered by dependency; each is one PR off `main`,
green on every gate, with no `2×` surviving a PR.

## 0. Where the codebase stands, and where it ends up

**Now.** Completeness laws are continuation-passing triples at a `Prover c` tag
(`Backend/WP.lean`: `Prover`, `Prover.instWP`, `Complete`, `complete_spec_iff`),
proved by `mvcgen` walks. The state carries freshness only (`ProverState.fresh :
env.FreshFrom nv`); reads are partial (`x.eval env : Except`), so every precondition
says `(x.eval env).isOk` and every promise quantifies the value it cannot name
(`∀ v, x.eval env = .ok v → …`). Witness blocks are `ReaderT (Assignments F) (Except
EvalError)`, a function of the table. The reading of a bundle exists three times
(`WitnessReads.Reads` with six instances, `Snarky.Reads`, `Sponge.Reads`) plus
`ReadsBit`. Census (non-blank lines after `:= by`): 58 `*_complete_spec`, 3101 lines,
1066 transport/pinning tokens (`eval_le`, `Le.trans`, `hle*`, `.mono`, `isOk_of_eq`,
`CVar.evalOk`, `ReadsBit`, `.isOk`); the four largest against their soundness twins:
`varBaseMul` 296/52, `endoMul` 276/46, `groupMapCircuit` 212/56, `verifyCircuit`
208/82.

**After.** A gadget's completeness law is a run equation at an invariant-carrying
state, `prove holds (g …) st.nv st.env = .ok ((gRun st …).out r)`, composed by
`prove_bind` and loop inductions with a state function. Scope is `x ∈ st` — the slot
is assigned — with a law set; an in-scope read is total (`toValuation`), a scoped
witness block cannot fail, and no proof mentions that names are numbers. The state's
invariant stays `FreshFrom`. Witness blocks are syntax
(`AsProver` as an inductive) with an evaluation `eval` and `run_eq_eval`. There is one
reading, `readVal`, at two valuations — arbitrary `V` for soundness,
`env.toValuation` for completeness. The prover `WP` instance, `Complete`, the bridge,
and every CPS completeness law are gone. `solve_complete` and the Schnorr boundary
consume run equations directly.

**The course's verdict this rests on** (Ch8 §8.9, Ch9 §9.5): forward proofs are
shorter than backward ones on every gadget (`double` 4/10, `select` 7/17, `isZero`
21/47); the difference is not text per call but what had to be invented (continuation,
`Le` conjunct, pinning, `Stable`, frame); and the backward side *grew* when values
left the statements, because a promise stated at the exit must be moved by `get_of_le`
per reading per state, which no search removes. §9.6: keep deployed statements as
corollaries; change the working form.

## 1. Name map, course → codebase

| course (`Hoare/`) | codebase (`Snarky/`) | note |
| --- | --- | --- |
| `Wit F α` (`pure`, `read v k`) | `AsProver F α` (`pure`, `read (x : CVar F) k`, `throw e`) | `throw` kept: `Field.lean:69` (`inv` at zero) uses it |
| `Wit.run`, `Wit.pure_eq/bind_eq/bind_pure/bind_read` | `AsProver.run`, same four `@[simp]` normal forms | do-blocks normalise to constructors |
| `readVar (v : Var)` | `AsProver.readCVar (x : CVar F) := .read x .pure` | typed `readVar` rebuilt by structural recursion over `varToFields` |
| `Assignments.get` | `Assignments.toValuation` (exists, `Assignments.lean:47`) | default `0` |
| `Assignments.Dom` (invariant) | — | not ported: the seam reserves the output slots below the counter (`compileBody`), so "defined exactly below the counter" is false there; `FreshFrom` stays the invariant |
| `x ∈ st := x < st.nv` | `v ∈ st := (st.env v).isSome` | the course's Option B: in scope *means* assigned; the same seven laws |
| `ProverState.dom`, `@[ext]` | `ProverState.fresh` (exists), `@[ext]` | |
| `ProverState.extend x` | `ProverState.extendMany (xs : List F)` | `existsOp n` allocates `n` slots; `extendPairs_consecutive` made functional |
| `Membership Var (ProverState F)` | `Membership Variable (ProverState F)` | `Membership`'s element type is an out-param: one element type per collection |
| — | `CVar.Scoped st x`, `CircuitType.Scoped st cv` | structural; computed per leaf encoder like `readVal` |
| `new_mem_extend`, `mem_extend_iff`, `mem_of_le`, `get_eq`, `get_extend_new`, `get_extend_of_mem`, `get_of_le` | same names at `extendMany` / `toValuation` | the seven laws; arithmetic lives only in their proofs |
| `Wit.Scoped st`, `Wit.eval g`, `run_eq_eval`, `eval_congr` | `AsProver.Scoped st`, `AsProver.eval V : Except EvalError α`, same two theorems | `eval` is `Except` because of `throw`; `simp` reduces it to `.ok _` on throw-free blocks |
| `Constraint.check`, `prove_assertX` | `Checker.holds`, `prove_addConstraint` + `LawfulChecker` at `toValuation` | |
| `prove_witnessVar` | `prove_witness` (+ `LawfulCheckedType.check_run`) | the leaf allocates a bundle and runs its check |
| `prove_dom`, `prove_le` | `prove_dom` (from `prove_freshFrom`), `prove_assignments_le` (exists) | |
| `sumRun`, `prove_sumAll_loop` | `prove_mapAccumM`, `prove_generateVec` | state function a parameter; induction on the list |
| `Runs`, `Runs.eq`, `Runs.le` | beside `prove_bind` in `Backend/Prover.lean` | the exactness and growth laws; no `WP` needed |
| `ProverSpec` (unary), `proverSpec_iff` (`ok ∧ wlp`) | `Complete` (unary), `complete_spec_iff` (`ok ∧ wlp`), `WP.lean` prover section | the only CPS form between S4 and S5; deleted in S5 |
| `sp`, `gc_sp_wlp`, `sp_exact`, `sp_bind`, `triple_iff_ok_and_wlp` | not ported | no consumer; the argument lives in the course |
| `ProverM.read`, `Stable`, frame, `recall` | not ported | the backward route; the course keeps it as the argument |
| `readVal_fvar/prod/ofEquiv` | exist (`Read.lean`, `@[circuitVal]`) | become the only decomposition family |

## 2. Steps

### S1 — `AsProver` as syntax (course `04707b3`)

`Circuit/DSL/Monad.lean:57` — `abbrev AsProver := ReaderT (Assignments F) (Except
EvalError)` becomes

```lean
inductive AsProver (F : Type) : Type → Type
  | pure  : α → AsProver F α
  | read  : CVar F → (F → AsProver F α) → AsProver F α
  | throw : EvalError → AsProver F α
```

with `bind` by structural recursion, `Monad`/`LawfulMonad` as for `CircuitM`, the
`@[simp]` normal forms (`pure_eq`, `bind_eq`, `bind_pure`, `bind_read`, `bind_throw`),
`readCVar x := .read x .pure`, `throw`, and `run : AsProver F α → Assignments F →
Except EvalError α` with its three structural `@[simp]` equations. PS's `AsProver f r
a = AsProverCtx → Effect a` admits interception through the raw constructor and
`MonadEffect`, but no witness block does it and no catch is exported; the sanctioned
surface is `pure`/`bind`/`readCVar`/`throwAsProver`, which is the inductive. Same move
the port already made for `Snarky(..)` → `CircuitM`.

Touch set: `prove` (`Prover.lean:82,93`: `wit.run env`), `prove_witnessCore`, `witness`
(`Monad.lean:246`: `compute.map valueToFields` is functorial — unchanged text), the typed
`readVar` (`Monad.lean:253`: rebuild over `varToFields` by structural recursion so the
size is static and the dynamic length guard disappears), `readAll_ok`, `readVar_le`;
32 witness-block definitions in 12 files (do-notation, expected unchanged); 39
`ReaderT.bind/pure/run` simp sites in 10 files → the `AsProver` normal forms; 13 direct
`wit env` applications → `wit.run env`; `witness_complete_spec` (`WP.lean:804`).

Gotcha from the course: a theorem named `AsProver.run_pure` opens the namespace, so a
bare `pure` in its statement is the *constructor*; state the `Pure.pure` form
explicitly or normalise first.

Accept: build; `snarky/scripts/check_axioms.sh` unchanged roots; deadcode; `lake
lint` (docBlame on the new constructors); shake; `check-style.sh`.

### S2 — `freshOp` leaves the fragment (done: #316)

`CircuitM.freshOp` allocated a variable without a value. No gadget, seam or script
ever emitted it, and the PS DSL's `fresh` has no caller in any gadget library:
allocation is `exists`, which computes before it allocates. The functionality is
subsumed, so parity with the ops record carries no weight: the constructor, `fresh`,
and one case per interpreter induction are gone; the parity table records the row as
outside the fragment.

`assignOp` stays. It is not unused: `compileBody`'s output back-fill writes the
reserved public output slots with `assignVars` after `main` has run. This is also
why S3 cannot carry the course's `Dom`: between the seed and the back-fill, the
output slots are unassigned *below* the counter, by the wire layout, not by any op.

### S3 — the total reading and scope (course `d868cbb`, `ada2466`, on Option B)

The course defined scope as "below the counter" and carried `Dom` (the table is
defined exactly below the counter). The codebase cannot: the seam leaves the reserved
output slots unassigned below the counter while `main` runs. The course's other
reading — §8.4's Option B — is what the contract actually needs: *in scope means
assigned*. So scope is assignment, the invariant stays `FreshFrom`, and every law
below holds with the same statement; `run_eq_eval`'s one need, `v ∈ st → st.env v =
some (st.env.toValuation v)`, is the definition.

`Backend/Assignments.lean`: `Assignments.extendList a nv xs` (the functional form of
`extendPairs_consecutive`, `WP.lean:719`) with `FreshFrom.extendList` and
`FreshFrom.le_extendList`; `toValuation_eq : (a v).isSome → a v = some (a.toValuation
v)`.

`Backend/Prover.lean`: `ProverState` keeps `fresh`, gains `@[ext]`;
`ProverState.extendMany (xs : List F)`; `instance : Membership Variable (ProverState F)
:= ⟨fun st v => (st.env v).isSome⟩`; `mem_lt : v ∈ st → v < st.nv` (from freshness,
used only in the laws' proofs); the laws —

```lean
theorem mem_extendMany_iff : v ∈ st.extendMany xs ↔ v ∈ st ∨ ∃ i < xs.length, v = st.nv + i   -- @[simp]
theorem mem_of_le (hle : st.env.Le st'.env) : v ∈ st → v ∈ st'
theorem get_eq (hv : v ∈ st) : st.env v = some (st.env.toValuation v)
theorem get_extendMany_new (hi : i < xs.length) : (st.extendMany xs).env.toValuation (st.nv + i) = xs[i]   -- @[simp]
theorem get_extendMany_of_mem (hv : v ∈ st) : (st.extendMany xs).env.toValuation v = st.env.toValuation v   -- @[simp]
theorem get_of_le (hle) (hv : v ∈ st) : st'.env.toValuation v = st.env.toValuation v
```

— `prove_freshFrom` and `freshOut` as they are; `prove_le` is `prove_assignments_le`.
The `iff` form of `mem_extendMany` is deliberate: `simp`'s default discharge depth is
2, so a conditional `mem_extend` lemma fails on towers deeper than two allocations; the
`iff` rewrites without discharging (course `ada2466`). `ProverState.extendMany`'s
projections are *not* simp lemmas: the `toValuation` laws match `(st.extendMany
xs).env` and must see it.

`Backend/Read.lean` becomes the scope module (it sits above `Prover.lean` and
`Types.lean`): `CVar.Scoped st : CVar F → Prop` (structural: `var v ↦ v ∈ st`, `const ↦
True`, `add`/`scale` ↦ components), `CVar.eval_eq_val : x.Scoped st → x.eval st.env =
.ok (x.val st.env.toValuation)` (the total read; `val_toValuation` is its converse),
`CircuitType.Scoped st cv := ∀ i, (varToFields cv)[i].Scoped st` with
`scoped_fvar/prod/ofEquiv/vector` computation lemmas, `Scoped.of_le`,
`Scoped.extendMany`, `readVal_of_le : cv.Scoped st → st.env.Le st'.env → readVal
st'.env.toValuation cv = readVal st.env.toValuation cv`, and

```lean
theorem readVal_extendMany_new [LawfulCircuitType F val var] (v : val) :
    readVal (st.extendMany (valueToFields v).toList).env.toValuation
      (fieldsToVar (mapVec CVar.var (allocRange st.nv (size F val)))) = v
```

by `vars_roundTrip`, `value_roundTrip`, `get_extendMany_new` — the one lemma every
`WitnessReads.reads_of_grant` instance was proving by hand per type.

`Circuit/DSL/Monad.lean`: `AsProver.Scoped st` (`read x k ↦ x.Scoped st ∧ ∀ v, (k
v).Scoped st`, `throw ↦ True`), `AsProver.eval (V : Valuation F) : AsProver F α → Except
EvalError α`, `run_eq_eval : w.Scoped st → w.run st.env = w.eval st.env.toValuation`,
`eval_congr`.

Accept: build + gates; `solve_complete`'s statement and the seam unchanged.
`Reads`/`WitnessReads` still exist at the end of S3; S4 deletes them.

### S4 — the conversion (course `a8568c2`, `50cd590`, `866f2e6`, `6b68f69`)

One PR. Its commits are by layer — backend, `Circuit/DSL`, `Kimchi/Circuit`,
`schnorr` — for review, not for separate landing. The diff is reported afterwards
(§S6); nothing in it is gated on a per-gadget number.

**Backend, `Prover.lean`.** Beside `prove_bind`: `prove_addConstraint : holds con
st.env = true → prove holds (addConstraint con) st.nv st.env = .ok (st.out ())`;
`prove_label`; `prove_witness` — for `w : AsProver F val`, `hs : w.Scoped st`, `hv :
w.eval st.env.toValuation = .ok v` (a `simp` fact on throw-free blocks), the leaf's run
is the check's run at the extended state, stated so that `check_run` closes it;
`Runs g st a st' := prove holds g st.nv st.env = .ok (st'.out a)`, `Runs.eq`
(exactness: `Runs g st a st' → prove … = .ok (T.out a') → a = a' ∧ st' = T`, by
`ProverState.ext`), `Runs.le` (`prove_assignments_le` on the graph).
`prove_mapAccumM` beside `mapAccumM` (`Kimchi/Circuit/Utils.lean:25`) and
`prove_generateVec` beside `generateVec` (`Vec.lean:32`): induction on the list with
the state function a parameter, the course's `prove_sumAll_loop` shape.

**Backend, `WP.lean`, prover section.** `LawfulChecker` (`:284`) fields restated at
the total reading — `check_r1cs : l.Scoped st → r.Scoped st → o.Scoped st → l.val V *
r.val V = o.val V → holds (r1cs l r o) st.env = true` at `V := st.env.toValuation` —
and the `Basic` instance and `KimchiConstraint.instLawfulChecker`
(`Kimchi/Semantics.lean:356`) with it. `LawfulCheckedType.check_complete` (`:627`)
becomes `check_run : cv.Scoped st → readVal st.env.toValuation cv = v → prove holds
(check cv) st.nv st.env = .ok (st.out ())`, with whatever value hypotheses the instance
carries today; 8 instances. `Complete` becomes the course's unary shape —

```lean
abbrev Complete (pre : ProverState F → Prop) (post : α → ProverState F → Prop) Q :=
  fun st => .up (pre st ∧ ∀ r st', post r st' → st.env.Le st'.env → (Q.1 r st').down)
```

— and `complete_spec_iff` reads `∀ st, pre st → ok g st ∧ wlp g post st`, with `ok` and
`wlp` as in the course (Ch9 §9.1). This is the only CPS form that may exist in the
tree from here on: a two-table promise `post env r env'` is never written again, and
any CPS statement S4 leaves behind is a five-line corollary of a run equation through
`complete_spec_iff`, `Runs.eq` and `Runs.le` (the course's
`select_complete_spec_forward`). The expected number of such statements after S4 is
zero; S5 is what that licenses.

**Every gadget, in its own file.** `g_run` beside `g_spec` (its soundness law):
scope hypotheses (`x.Scoped st`, `cv.Scoped st`), readings as `x.val
st.env.toValuation` / `readVal st.env.toValuation cv`, the state after as a term — the
explicit `extendMany` tower for short gadgets, a `def gRun (st …) : ProverState F`
mirroring the body for long ones (`scaleRound` allocates 26 cells; the `Reflect.lean`
run functions are the precedent). Composition is `simp only [g, prove_bind]`, one `rw`
per call, side goals `simp [hx]`, values closed terms of `st`. Loops (`varBaseMul`,
`endoMul`, the sponge's `foldBlocks`, `unpack`) by `prove_mapAccumM`/`prove_generateVec`
with their existing gate-side chains (`chainBuild`, …) as the state function and the
existing gate theorems (`chain_complete`, …) at the constraint checks. `g_complete_spec`
is deleted in the same commit. The 58 laws are in: `Circuit/DSL/{Field, Boolean,
Assert, Bits, UnpackFull, Utils}`, `Kimchi/Circuit/{AddComplete, CurvePoint, EndoMul,
EndoScalar, GroupMap, Poseidon, RandomOracle, RangeCheck, Sponge, VarBaseMul}`,
`Schnorr/Laws.lean`, `Example.lean`. `verifyCircuit_complete_spec` is already exported
in run form; only its internal `mvcgen` walk is replaced by a `verifyRun` state
function. `Boundary.complete` consumes `CurvePoint`'s `check_run` and `verifyCircuit`'s
run directly; its 13-line `hreads` block is one `simp [readVal_ofEquiv, readVal_prod,
readVal_fvar, h0, …]`.

**The readings.** `Read.lean`'s `Readable`, `Reads`, `ReadsAll`, `readable_*_iff`,
`reads_*_iff`, the three `.le`s, `exists_reads*`, `Reads.readable`, `Reads.unique`;
`WP.lean`'s `WitnessReads`, `ofEquiv`, six instances, `mapM_eval_*` helpers,
`ReadsBit` and its three lemmas; `Sponge.Reads`, `reads_init`, `reads_ofConstants`,
`Sponge.Reads.le` (the sponge reads as `Vals env.toValuation`); the Schnorr `Reads`
— all deleted. `readVal` and its `@[circuitVal]` lemmas are the reading.

**Manifests.** `snarky/roots.txt` (586 entries) and `snarky/scripts/check_axioms.lean`
(191 root names): `*_complete_spec` → `*_run`; `Snarky.Reads.le`,
`Snarky.WitnessReads.ofEquiv`, `Snarky.SpongeVar.Reads.le` removed; `prove_witness`,
`prove_addConstraint`, `prove_mapAccumM`, `prove_generateVec`, `Runs.eq`, `Runs.le`
added as interpreter laws.

Accept: build + all gates; the report of §S6 in the PR description.

### S5 — delete the prover `WP` apparatus

Decided. With no CPS consumer left after S4: `Prover` (`WP.lean:219`),
`Prover.instWP`/`instWPMonad`, `Complete`, `complete_spec_iff`, `ok`, `wlp`,
`KimchiProverC` (`Semantics.lean:368`), `witness_complete_spec`, `check_pure_complete`,
`generateVec_complete_spec`, `post_of_prove` (`WP.lean:1168`, once its consumers are
gone) are deleted; `roots.txt` (`Snarky.ProverC`, `Snarky.Prover.instWP`) and
`check_axioms.lean` with them. `WP.lean` keeps the soundness half (`Builder`,
`Builder.instWP`, `SoundCheckedType`, `witness_spec`, `builder_spec_iff`). The
`formal/CLAUDE.md` sentence on completeness laws stays true ("a successful prover run
satisfies every built constraint, plus the bind-composition laws");
`docs/snarky-ps-alignment.md` is updated where it names the deleted declarations.

This is the last commit of the S4 PR if the S4 tree already has no CPS consumer, and
its own PR otherwise.

### S6 — the report

In the S4 PR description: per law, CPS lines before → run-equation lines after; the
totals against the baseline (58 / 3101 / 1066); the four twins (`varBaseMul` 296 → ?,
`endoMul` 276 → ?, `groupMapCircuit` 212 → ?, `verifyCircuit` 208 → ?) beside their
soundness laws (52 / 46 / 56 / 82); and the per-file `Reads` vocabulary counts
(VarBaseMul 60, Field 42, Boolean 38, RandomOracle 35, Sponge 33, EndoMul 33, …), which
should be zero. The tax-token count should be zero by construction — `Le` occurs only
in `Runs.le`, `get_of_le`, `readVal_of_le`. Any law whose run equation came out longer
than its CPS law is listed as such. Decision, small: commit the census script
(`formal/scripts/proof-lines.py`) so the number is reproducible, or keep it out.

## 3. Risks, with the fallback for each

- **Towers of 26.** `scaleRound`'s state is 26 cells deep. The course measured
  `isZero` (6 deep) at 21 lines with the membership laws; at 26 the `simp [hx]` tower
  reads are linear in depth but the state *term* is not readable. Fallback: the state
  function `scaleRoundRun` as a `def` (Reflect.lean precedent); the theorem's right side
  is then one name.
- **Throwing blocks.** `inv` throws at zero, so `AsProver.eval` is `Except`-valued and
  `prove_witness` carries `hv : w.eval … = .ok v`. On every other block `simp` reduces
  the left side to `.ok _`; on `inv` the hypothesis is the `x ≠ 0` the law already has.
- **Checker side conditions.** `holds con st.env = true` at a tower is the gate model's
  `ok` on cells read at `toValuation`; this is where `chain_complete` and friends are
  applied, exactly as today. The `LawfulChecker` restatement is what makes the reads
  total there.
- **`rw` and delayed tactic blocks.** A `rw [prove_g _ (by simp [hx])]` elaborates the
  block after unification, so side goals at the current state work; a `have h :=
  prove_g _ (by …)` does not (course gotcha). Values need no pinning now, so the `(v
  := …)` form disappears; keep to `rw` chains.
- **Kernel reducibility.** `solve` is executable and validated by `decide`; `extendList`
  replaces `extendPairs` only in *statements*, not in `solve`'s definition. `Dom` is a
  `Prop`. Nothing on the executable path changes shape.
- **`Membership` is one element type per collection.** `v ∈ st` is for `Variable`
  only; `CVar.Scoped st`, `CircuitType.Scoped st`, `AsProver.Scoped st` are predicates.
- **The ghost-entry failure is not revisited.** The course established (Ch8 §8.4, by
  experiment) that `mvcgen` mis-assigns an entry-state ghost; nothing here puts a
  two-state promise back into a native triple.

## 4. Process

One PR per step, branch off `main`, stacked only where a step's build needs the prior
step. Per commit: `lake build Snarky` (from `formal/`, the one build — iterate by
per-file LSP diagnostics, not by rebuilding), `snarky/scripts/check_axioms.sh`, the
deadcode gate, `lake lint`, `lake exe shake` with an absolute `--cfg`,
`scripts/check-style.sh`. Names change only with `roots.txt` and `check_axioms.lean` in
the same commit.
