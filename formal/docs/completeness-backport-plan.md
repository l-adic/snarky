# Completeness backport plan — the course's prover machinery into `formal/snarky`

Source of truth: the course `martyall/wp`, `main` after PR #1 (`aa8792f` … `6b68f69`). The
course built and measured, on a five-gadget toy, the formulation of completeness that
this plan carries into the codebase. File and line references are at `sound-native`
(`1ffa348e`), which stacks on PRs #313 and #314; the backport starts after those land,
and keeps the soundness half `sound-native` introduced (`Builder V`, `SoundCheckedType`,
`witness_spec`) untouched. Every step below names the course commit it
inherits from, the codebase files it touches, the numbers it is judged by, and the
decision it needs, if any. Steps are ordered by dependency; each is one PR off `main`,
green on every gate, with no `2×` surviving the PR except the transitional items S6
marks and S7 removes.

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
`prove_bind` and loop inductions with a state function. The invariant is the domain
(`Dom`: defined exactly below the counter), so an in-scope read is total
(`toValuation`) and a scoped witness block cannot fail. Scope is `x ∈ st` with a law
set; no proof mentions that names are numbers. Witness blocks are syntax
(`AsProver` as an inductive) with an evaluation `eval` and `run_eq_eval`. There is one
reading, `readVal`, at two valuations — arbitrary `V` for soundness,
`env.toValuation` for completeness. The prover `WP` instance, `Complete`, and every
CPS completeness law are gone (or, per the S7 decision, the forward calculus stays as
rooted certificates). `solve_complete` and the Schnorr boundary consume run equations
directly.

**The course's verdict this rests on** (Ch8 §8.9, Ch9 §9.5): forward proofs are
shorter than backward ones on every gadget (`double` 4/10, `select` 7/17, `isZero`
21/47), the difference is not text per call but what had to be invented (continuation,
`Le` conjunct, pinning, `Stable`, frame), and the backward side *grew* when values
left the statements because a promise stated at the exit must be moved by `get_of_le`
per reading per state, which no search removes. §9.6: keep deployed statements as
corollaries; change the working form.

## 1. Name map, course → codebase

| course (`Hoare/`) | codebase (`Snarky/`) | note |
| --- | --- | --- |
| `Wit F α` (`pure`, `read v k`) | `AsProver F α` (`pure`, `read (x : CVar F) k`, `throw e`) | `throw` kept: `Field.lean:69` (`inv` at zero) uses it |
| `Wit.run`, `Wit.pure_eq/bind_eq/bind_pure/bind_read` | `AsProver.run`, same four `@[simp]` normal forms | do-blocks normalise to constructors |
| `readVar (v : Var)` | `AsProver.readCVar (x : CVar F) := .read x .pure` | typed `readVar` rebuilt by structural recursion over `varToFields` |
| `Assignments.get` | `Assignments.toValuation` (exists, `Assignments.lean:47`) | default `0` |
| `Assignments.Dom` | `Assignments.Dom` (new), replaces `FreshFrom` | `∀ v, (a v).isSome ↔ v < nv` |
| `ProverState.dom`, `@[ext]` | same | `freshOut` → `domOut` |
| `ProverState.extend x` | `ProverState.extendMany (xs : List F)` | `existsOp n` allocates `n` slots; `extendPairs_consecutive` made functional |
| `x ∈ st` (`Membership Var`) | `v ∈ st` (`Membership Variable`) | `Membership`'s element type is an out-param: one element type per collection |
| — | `CVar.Scoped st x`, `CircuitType.Scoped st cv` | structural; computed per leaf encoder like `readVal` |
| `new_mem_extend`, `mem_extend_iff`, `mem_of_le`, `get_eq`, `get_extend_new`, `get_extend_of_mem`, `get_of_le` | same names at `extendMany` / `toValuation` | the seven laws; arithmetic lives only in their proofs |
| `Wit.Scoped st`, `Wit.eval g`, `run_eq_eval`, `eval_congr` | `AsProver.Scoped st`, `AsProver.eval V : Except EvalError α`, same two theorems | `eval` is `Except` because of `throw`; `simp` reduces it to `.ok _` on throw-free blocks |
| `Constraint.check`, `prove_assertX` | `Checker.holds`, `prove_addConstraint` + `LawfulChecker` at `toValuation` | |
| `prove_witnessVar` | `prove_witness` (+ `LawfulCheckedType.check_run`) | the leaf allocates a bundle and runs its check |
| `prove_dom`, `prove_le` | `prove_dom` (from `prove_freshFrom`), `prove_assignments_le` (exists) | |
| `sumRun`, `prove_sumAll_loop` | `prove_mapAccumM`, `prove_generateVec` | state function a parameter; induction on the list |
| `Runs`, `ok`, `wlp`, `sp`, `Runs.eq`, `Runs.le`, `triple_iff_ok_and_wlp`, `proverSpec_iff` | `Backend/Forward.lean` (new) | transitional tooling; certificates per S7 |
| `ProverM.read`, `ProverSpec`, `Stable`, frame, `recall` | not ported | the backward route; the course keeps it as the argument |
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

with `bind` by structural recursion, `Monad`/`LawfulMonad` as for `CircuitM`, the four
`@[simp]` normal forms (`pure_eq`, `bind_eq`, `bind_pure`, `bind_read`, plus
`bind_throw`), `readCVar x := .read x .pure`, `throw`, and `run : AsProver F α →
Assignments F → Except EvalError α` with its three structural `@[simp]` equations.
PS's `AsProver f r a = AsProverCtx → Effect a` admits interception through the raw
constructor and `MonadEffect`, but no witness block does it and no catch is exported;
the sanctioned surface is `pure`/`bind`/`readCVar`/`throwAsProver`, which is the
inductive. Same move the port already made for `Snarky(..)` → `CircuitM`.

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
lint` (docBlame on the new constructors); shake; `check-style.sh`. No measurement.

### S2 — the fragment: `freshOp` / `assignOp`

`Dom` (S3) is an invariant of every run only if nothing allocates without a value.
`CircuitM.freshOp` does, and `assignOp` fills later. No gadget emits either: nothing
outside `Backend/` and `DSL/Monad.lean` mentions `fresh`, `assignVars`, `existsVars`;
every allocation is `witness = existsOp`, which computes before it allocates (PS
`exists`, `Monad.purs:321`, is the same single op). The PS gadget libraries in scope
(`snarky`, `snarky-kimchi`, `poseidon`, `random-oracle`, `schnorr`) never call PS
`fresh`/`assignVars` either.

**Decision.** (a) Remove `freshOp`, `assignOp`, `fresh`, `assignVars` from the modeled
fragment — recommended: the ops record keeps them in PS, the port documents the two
rows as outside the fragment (`DSL.lean` parity table, `Snarky.lean` preamble,
`docs/snarky-ps-alignment.md`), and `Dom` is an interpreter invariant. (b) Keep them and
add `CircuitM.NoFresh` (one lemma per combinator, `forIn`/`mapAccumM` included) as a
hypothesis of `prove_dom`. (a) deletes ~80 lines and two cases from every interpreter
induction; (b) adds a predicate that every law must carry.

Touch set under (a): `CircuitM`, `CircuitM.bind`, `build`, `prove`, `prove_bind`,
`prove_freshFrom`, `prove_assignments_le`, `prove_nextVar_le`, `prove_build_agrees`,
`prove_complete`, `build_eraseWitness`, the three doc sites. `check_cs_equality` is
unaffected (gadget programs never contained the ops).

Accept: build + all gates; parity table updated in the same commit.

### S3 — the domain invariant, the total reading, scope (course `d868cbb`, `ada2466`)

`Backend/Assignments.lean`: `protected def Assignments.Dom (a) (nv) : Prop := ∀ v, (a
v).isSome ↔ v < nv`; `Dom.lt_of_assigned`; `Dom.toValuation_eq : a.Dom nv → v < nv → a
v = some (a.toValuation v)` (the course's `get_eq`); `Assignments.extendList a nv xs`
(the functional form of `extendPairs_consecutive`, `WP.lean:719`) with
`Dom.extendList : a.Dom nv → (a.extendList nv xs).Dom (nv + xs.length)` and
`Dom.le_extendList`. `FreshFrom` is replaced, not kept beside: `Compile.lean:171–204`
(`solve_seed`) produces `Dom A.size`, which the seed satisfies by construction.

`Backend/Prover.lean`: `ProverState` gets `dom : env.Dom nv` in place of `fresh`, and
`@[ext]`; `ProverState.extendMany (xs : List F)`; `instance : Membership Variable
(ProverState F) := ⟨fun st v => v < st.nv⟩`, the one place `<` appears; the laws —

```lean
theorem mem_extendMany_iff : v ∈ st.extendMany xs ↔ v ∈ st ∨ ∃ i < xs.length, v = st.nv + i   -- @[simp]
theorem mem_of_le (hle : st.env.Le st'.env) : v ∈ st → v ∈ st'
theorem get_eq (hv : v ∈ st) : st.env v = some (st.env.toValuation v)
theorem get_extendMany_new (hi : i < xs.length) : (st.extendMany xs).env.toValuation (st.nv + i) = xs[i]   -- @[simp]
theorem get_extendMany_of_mem (hv : v ∈ st) : (st.extendMany xs).env.toValuation v = st.env.toValuation v   -- @[simp]
theorem get_of_le (hle) (hv : v ∈ st) : st'.env.toValuation v = st.env.toValuation v
```

— `prove_dom` (rewrite of `prove_freshFrom` for the iff), `domOut`. `prove_le` is
`prove_assignments_le`. The `iff` form of `mem_extendMany` is deliberate: `simp`'s
default discharge depth is 2, so a conditional `mem_extend` lemma fails on towers
deeper than two allocations; the `iff` rewrites without discharging (course `ada2466`).
`ProverState.extendMany`'s projections are *not* simp lemmas: the `toValuation` laws
match `(st.extendMany xs).env` and must see it.

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

Accept: build + gates; `solve_complete`'s statement unchanged. `Reads`/`WitnessReads`
still exist at the end of S3 (deleted in S6 as their consumers convert).

### S4 — the run-equation primitives (course `a8568c2` Ch7 §7.3–7.4)

`Backend/Prover.lean`, beside `prove_bind`:

- `prove_addConstraint : holds con st.env = true → prove holds (addConstraint con)
  st.nv st.env = .ok (st.out ())`; `prove_label`.
- `prove_witness`: for `w : AsProver F val`, `hs : w.Scoped st`, `hv :
  w.eval st.env.toValuation = .ok v` (a `simp` fact on throw-free blocks), the leaf's
  run is the check's run at the extended state:
  `prove holds (witness w) st.nv st.env = (prove holds (check (fieldsToVar …)) (st.nv +
  size) (st.extendMany (valueToFields v).toList).env).map …` — stated so that
  `LawfulCheckedType.check_run` closes it.
- `LawfulCheckedType.check_complete` (`WP.lean:627`) restated as `check_run :
  cv.Scoped st → readVal st.env.toValuation cv = v → prove holds (check cv) st.nv st.env
  = .ok (st.out ())`, with whatever value hypotheses the instance carries today; 8
  instances.
- `LawfulChecker` (`WP.lean:284`) fields restated at the total reading: `check_r1cs :
  l.Scoped st → r.Scoped st → o.Scoped st → l.val V * r.val V = o.val V → holds (r1cs l
  r o) st.env = true` at `V := st.env.toValuation`; the `Basic` instance and
  `KimchiConstraint.instLawfulChecker` (`Kimchi/Semantics.lean:356`).
- `prove_mapAccumM` beside `mapAccumM` (`Kimchi/Circuit/Utils.lean:25`) and
  `prove_generateVec` beside `generateVec` (`Vec.lean:32`): induction on the list with
  the state function a parameter, the course's `prove_sumAll_loop` shape. These replace
  `generateVec_complete_spec` (`WP.lean:1118`) once its consumers convert.

Accept: build + gates. The primitives have no consumer yet; root them in
`check_axioms.lean` (`prove_witness`, `prove_addConstraint`, `prove_mapAccumM`,
`prove_generateVec`) so the deadcode gate passes, as interpreter laws are rooted today.

### S5 — the bridge tooling (course `866f2e6`, `6b68f69`)

`Backend/Forward.lean` (new, imports `WP.lean`): `Runs g st a st' := prove holds g
st.nv st.env = .ok (st'.out a)`, `Runs.eq` (exactness: `Runs g st a st' → prove … =
.ok (T.out a') → a = a' ∧ st' = T`, by `ProverState.ext`), `Runs.le`
(`prove_assignments_le` on the graph). `complete_spec_iff` keeps its statement
(binary `Complete`, `post st.env r st'.env ∧ Le`) — restating `Complete` unary would
touch all 58 CPS specs that S6 deletes, for nothing. With `Runs.eq` and `Runs.le`, a
run equation yields a CPS corollary in the course's five lines
(`select_complete_spec_forward`): `complete_spec_iff.mpr`, `⟨_, h⟩` for non-failure,
`hr.eq h` to land at the written-out state, the promise read off it, `hr.le`.

This is transitional tooling for S6. Whether `ok`, `wlp`, `sp`, `triple_iff_ok_and_wlp`,
`gc_sp_wlp`, `sp_exact`, `sp_bind` join it is the S7 decision.

### S6 — gadget run equations, bottom-up

Per gadget `g`: a theorem `g_run` beside `g_spec` (its soundness law — family
placement), stated with scope hypotheses (`x.Scoped st`, `cv.Scoped st`), readings as
`x.val st.env.toValuation` / `readVal st.env.toValuation cv`, and the state after as a
term — the explicit `extendMany` tower for short gadgets, a `def gRun (st …) :
ProverState F` mirroring the body for long ones (`scaleRound` allocates 26 cells; the
`Reflect.lean` run functions are the precedent: let-mirror the body). Composition is
`simp only [g, prove_bind]` then one `rw` per call, side goals `simp [hx]`, values
closed terms of `st` (no `(v := …)` pinning). The gadget's `g_complete_spec` is deleted
in the same commit when no CPS consumer remains; otherwise it becomes the five-line
corollary of S5 until its last consumer converts, and is deleted then. `Reads`,
`WitnessReads`, `ReadsBit`, `Sponge.Reads`, the Schnorr `Reads`, `Read.lean`'s
`readable_*_iff`/`reads_*_iff`/`.le`/`exists_reads*`/`Reads.unique`, and
`WP.lean`'s `mapM_eval_*` helpers are deleted as their last consumers convert.

Order, with each law's current length as its baseline:

1. DSL leaves, `Circuit/DSL/` — Field (`mul` 34, `inv` 24, `div` 17, `square` 23,
   `equals` 33, `neq` 20, `pow` 1, `powGo` 70), Boolean (`and` 10, `or` 20, `xor` 41,
   `select` 36, `all` 56, `any` 55), Assert (9 laws, 4–21), Utils `sealVar` 47, Bits
   `unpack` 60, UnpackFull (31, 54, 17). Expect most to be one `simp`.
2. `Kimchi/Circuit/` leaves — AddComplete (`sealPoint` 12, `addFastTail` 82, `addFast`
   85), `CurvePoint.check` (the `LawfulCheckedType` instance), EndoScalar `toField` 61,
   RangeCheck 10.
3. The ladders — VarBaseMul `splitFieldVar` 33, **`scaleRound` 137 → predict ≤ 45,
   refute > 90 or any `Le` in the proof**; **`varBaseMul` 296 → the loop by
   `prove_mapAccumM` with `chainBuild` as the state function and `chain_complete` at
   the constraint check; predict 100–120, refute > 200**; `scaleFast1` 6, `scaleFast2`
   133, `scaleFast2'`; EndoMul (`endoInv` 153, `endoMulRound` 46, `endoMul` 276);
   GroupMap (`sqrtFlagged` 52, `groupMapCircuit` 212, `toGroup` 24). **Go/no-go here**:
   if `scaleRound` or `varBaseMul` exceeds its threshold, stop, report, and leave the
   remaining CPS laws in place — S7 does not happen.
4. The sponge tower — Poseidon 72, Sponge (`addSlotVar` 73, `absorb` 73, `squeeze` 51),
   RandomOracle (`update` 7, `updateBlock` 21, `foldBlocks`, `hash2` 24, `hashVec` 14).
   `Sponge.Reads` collapses to `Vals env.toValuation`; `reads_init`/`reads_ofConstants`
   become `vals_init`/`vals_ofConstants` at the completed table.
5. Schnorr — `verifyCircuit` (208; predict ≈ the soundness twin, 82): a `verifyRun`
   state function; the exported statement (`Laws.lean:141`) is already run-form, so its
   text does not change. `Boundary.complete` consumes `CurvePoint`'s `check_run` and
   `verifyCircuit`'s run directly; its 13-line `hreads` block is one `simp
   [readVal_ofEquiv, readVal_prod, readVal_fvar, h0, …]`.
6. `Example.lean` (`cubic` 28).

Expected end of S6: every reading is `readVal`/`val` at `toValuation`; the 1066-token
tax is zero by construction (no `Le` in any gadget proof; `Le` appears only in
`Runs.le`, `get_of_le`, `readVal_of_le`); the per-file `Reads` vocabulary counts
(VarBaseMul 60, Field 42, Boolean 38, RandomOracle 35, Sponge 33, EndoMul 33, …) go to
zero.

### S7 — delete the prover `WP` apparatus, or root it

With no CPS consumer left, `Prover` (`WP.lean:219`), `Prover.instWP`/`instWPMonad`,
`Complete`, `complete_spec_iff`, `KimchiProverC` (`Semantics.lean:368`),
`witness_complete_spec`, `check_pure_complete`, `generateVec_complete_spec`,
`post_of_prove` (`WP.lean:1168`, if its consumers are gone), and the transitional
`Forward.lean` tooling are dead. `WP.lean` keeps the soundness half (`Builder`,
`Builder.instWP`, `SoundCheckedType`, `witness_spec`, `builder_spec_iff`).

**Decision.** (a) Delete all of it — recommended under dead = 0 and no 2×; the argument
lives in the course. (b) Keep `Forward.lean` as rooted certificates: `ok`, `wlp`, `sp`,
`triple_iff_ok_and_wlp`, `sp_exact`, `Runs.eq`, and `complete_spec_iff` in `ok ∧ wlp`
form — the codebase's own statement that its completeness laws are `sp` laws and that
a CPS triple is their corollary. (b) costs ~120 lines and a `Prover.instWP` that
nothing else uses.

Touch set: `snarky/roots.txt` (586 entries; `Snarky.ProverC`, `Snarky.Prover.instWP`,
`Snarky.Reads.le`, `Snarky.WitnessReads.ofEquiv`, every `*_complete_spec` →
`*_run`), `snarky/scripts/check_axioms.lean` (191 root names, same renames),
`docs/snarky-ps-alignment.md`, the `formal/CLAUDE.md` sentence on completeness laws
(still true: "a successful prover run satisfies every built constraint, plus the
bind-composition laws").

### S8 — measure and record

Re-run the census on the final tree; the PR description carries before/after per
gadget and the four twins (`varBaseMul` 296 → ?, `endoMul` 276 → ?, `groupMapCircuit`
212 → ?, `verifyCircuit` 208 → ?). **Decision**: commit the census script
(`formal/scripts/proof-lines.py`, lines after `:= by` per theorem, by name pattern)
so the number is reproducible, or keep it out of the tree.

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
  applied, exactly as today. The `LawfulChecker` restatement (S4) is what makes the
  reads total there.
- **`rw` and delayed tactic blocks.** A `rw [prove_g _ (by simp [hx])]` elaborates the
  block after unification, so side goals at the current state work; a `have h :=
  prove_g _ (by …)` does not (course gotcha). Values need no pinning now, so the `(v
  := …)` form disappears; keep to `rw` chains.
- **Kernel reducibility.** `solve` is executable and validated by `decide`; `extendList`
  replaces `extendPairs` only in *statements*, not in `solve`'s definition. `Dom` is a
  `Prop`. Nothing on the executable path changes shape.
- **`Membership` is one element type per collection.** `v ∈ st` is for `Variable`
  only; `CVar.Scoped st`, `CircuitType.Scoped st`, `AsProver.Scoped st` are predicates.
- **Mixing during S6.** A CPS consumer that receives a converted gadget's law through
  the bridge sees an exact run, so no `Le` is reintroduced on that edge; the consumer's
  *own* proof keeps its `Le` until it converts. Convert bottom-up and the mixing is
  bounded to one layer at a time.
- **The ghost-entry failure is not revisited.** The course established (Ch8 §8.4, by
  experiment) that `mvcgen` mis-assigns an entry-state ghost; nothing here puts a
  two-state promise back into a native triple.

## 4. Process

One PR per step, branch off `main`, stacked only where a step's build needs the prior
step. Per commit: `lake build Snarky` (from `formal/`, the one build — iterate by
per-file LSP diagnostics, not by rebuilding), `snarky/scripts/check_axioms.sh`, the
deadcode gate, `lake lint`, `lake exe shake` with an absolute `--cfg`,
`scripts/check-style.sh`. Names change only with `roots.txt` and `check_axioms.lean` in
the same commit. The course's measurement discipline applies: every converted gadget's
PR quotes the before/after line count beside the statement, and the S6 go/no-go is
the stated threshold, not a judgement call.
