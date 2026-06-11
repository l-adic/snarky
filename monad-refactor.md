# Direct-to-Effect circuit interpreters (kill the double Run interpretation)

## Context

Heap-churn profiling (2026-06-11, see `prof/heap-churn-preload.mjs` /
`prof/analyze_heapprofile.py`) attributed **42–54% of all allocation**
(≈13–17 GB of each ~31 GB bench trial) to `Run`/`Free`/`CatList` machinery:

- `runCircuitBuilder` / `runCircuitProver` interpret the reified
  `Run (CIRCUIT f c r)` program into *another* `Run (EFFECT + r)` program,
  which is then peeled again by `Run.runBaseEffect`;
- `Run.Except` / `Run.Reader` handler layers add further full passes, and
  `runAsProver` allocates a fresh `runExcept <<< runReader` handler chain
  **per `exists`**.

The fix: interpret **directly into `Effect`**, with the open advice tail `r`
discharged by a caller-supplied handler. The `Snarky` / `AsProver` *program
representation stays Run-based* — this is NOT a final-tagless rewrite; only
the interpreters and everything downstream of them change. Error channels
(`EXCEPT EvaluationError`; `ProveError` is a synonym, `Pickles/Prove/
Compile.purs:187`) become explicit `Either EvaluationError` returns.

Constraint: the advice row is genuinely used — the example app's
`MERKLE`/`ACCOUNT_MAP`/`TRANSACTION` effects route through pickles' provers,
and test-utils has `FACTOR` — so the row parameter survives. Pickles keeps
threading `r`, but as a handler *value* instead of extra Run layers. Pickles
itself never uses `r` (always `()` in its own tests/bench).

Expected outcome: the CatList/CatQueue/Free slice of the churn profile
collapses; wall-time win on both bench groups (baseline to beat:
`bench-results/2131445f5-2026-06-11T22-30-54-362Z.json`, compile 6.54 s /
prove 8.51 s steady-state).

## Core design

### The handler type — newtype, not a synonym

New module `packages/snarky/src/Snarky/Backend/Advice.purs`:

```purescript
newtype AdviceHandler :: Row (Type -> Type) -> Type
newtype AdviceHandler r = AdviceHandler (VariantF r ~> Effect)

runAdviceHandler :: forall r a. AdviceHandler r -> VariantF r a -> Effect a
runAdviceHandler (AdviceHandler f) = f

noAdvice :: AdviceHandler ()
noAdvice = AdviceHandler case_     -- Data.Functor.Variant.case_ (re-exported by Run)
```

Newtype because the handler is **stored** — in `RuleEntry` record fields and
prover carrier tuples — and PS rejects rank-2 storage at the record-field
level (this codebase already documents that at `Pickles/Prove/Compile.purs:3113`).
The rank-2 polymorphism is real: one handler value is applied both at the
circuit row (`x = Run (CIRCUIT f c r) a`) and inside `Exists` at the witness
row (`x = Run (ASPROVER f r) (Array f)`). The newtype is erased by
purs-backend-es. Re-export `AdviceHandler`/`noAdvice` from `Snarky.Circuit.DSL`.

### Interpreter loop shape

Verified against run-5.0.0 (in `.spago`):
`Run.peel :: Run r a -> Either (VariantF r (Run r a)) a`; `Run.on`/`case_`
are re-exported `Data.Functor.Variant` combinators; Run does **not** export
an `_effect` proxy — define `Proxy :: Proxy "effect"` locally. No
`Except.catch`/`Reader.local` anywhere in the repo, so hard-coding
throw-short-circuits and constant-env in the loops is semantics-preserving.

```purescript
-- tailRecM in Effect (MonadRec Effect = JS loop, stack-safe).
-- Unwrap the AdviceHandler ONCE outside the loop so the hot loop closes
-- over a plain function.
runAsProver (AdviceHandler handler) env (AsProver m0) = tailRecM go m0
  where
  _effect = Proxy :: Proxy "effect"
  go m = case Run.peel m of
    Right a -> pure (Done (Right a))
    Left v ->
      v # on _except (\(Except e) -> pure (Done (Left e)))
        ( on _reader (\(Reader k) -> pure (Loop (k env)))
            ( on _effect (\eff -> Loop <$> eff)
                (\other -> Loop <$> handler other)
            )
        )
```

Peel order matters and works syntactically: `CIRCUIT f c r =
(circuit :: CircuitF f c r | EFFECT + r)`, so `on _circuit` leaves
`VariantF (EFFECT + r)`, `on _effect` leaves exactly `VariantF r` for the
handler. For ASPROVER: `_except`, `_reader`, `_effect`, then handler.

## New signatures — snarky core

`packages/snarky/src/Snarky/Circuit/DSL/Monad.purs`:

```purescript
runAsProver :: forall f r a. AdviceHandler r -> Assignments f -> AsProver f r a
            -> Effect (Either EvaluationError a)
```

Delete `liftEffectRow`. `AsProver`, `Snarky`, `CircuitF`, `CIRCUIT`,
`ASPROVER`, `liftAdvice`, `exists` unchanged.

`packages/snarky/src/Snarky/Backend/Builder.purs`:

```purescript
runCircuitBuilder
  :: forall f c c' aux r a
   . CompileCircuit f c c' aux
  => AdviceHandler r
  -> CircuitBuilderState c aux
  -> Run (CIRCUIT f c' r) a
  -> Effect (Tuple a (CircuitBuilderState c aux))
-- execCircuitBuilder: same, returning Effect (CircuitBuilderState c aux)
```

Loop arms keep their case structure, minus every `Run.liftEffect` wrapper;
`Run.send other` splits into the `_effect` arm + the handler fallthrough.
`Exists` continues to discard the witness; the handler param is still needed
because circuit code *can* lift advice ops outside `exists` (the example's
compile-time panic handlers rely on this).

`packages/snarky/src/Snarky/Backend/Prover.purs`:

```purescript
runCircuitProver
  :: forall f c r a
   . SolveCircuit f c
  => AdviceHandler r
  -> ProverState f
  -> Run (CIRCUIT f c r) a
  -> Effect (Tuple (Either EvaluationError a) (ProverState f))
```

`Exists n w k` / `Assign vars w k` arms call the new
`runAsProver handler s.assignments (AsProver w)` — this is the rank-2 point;
a monomorphized handler fails to typecheck here first.
`SolveCircuit.proverConstraint` is already Effect-based — unchanged.

`packages/snarky/src/Snarky/Backend/Compile.purs`:

```purescript
compile' :: ... => AdviceHandler r -> { debug :: Boolean }
         -> Proxy a -> Proxy b -> Proxy c'
         -> (avar -> Snarky f c' r bvar)
         -> Effect (CircuitBuilderState c aux)
compile  :: ... (same, debug=false)

type SolverT f c r a b =
  AdviceHandler r -> a -> Effect (Either EvaluationError (Tuple b (Assignments.Frozen f)))
type Solver f c a b = SolverT f c () a b

makeSolver' :: ... => { debug :: Boolean } -> Proxy c
            -> (avar -> Snarky f c r bvar) -> SolverT f c r a b
runSolver :: Solver f c a b -> a -> Effect (Either EvaluationError (Tuple b (Assignments.Frozen f)))
runSolver s = s noAdvice
```

**Delete** `runSolverT` (a `SolverT` is now directly runnable) and the unsafe
`liftExceptRow` row-widening hack. `makeSolver'` body becomes a plain Effect
do-block threading `Either` manually.

## New signatures — pickles

### Handler entry points

- **Compile phase**: explicit `AdviceHandler r` argument on `compileMulti`,
  `runMultiCompileFull`, and the `CompilableRulesSpecShape` /
  `CompilableRulesSpec` class methods (`prePassDomainLog2s`,
  `runMultiCompile`, `runStepCompiles`); all return `Effect ...` instead of
  `Run (EFFECT + r) ...`. Not a `CompileMultiConfig` field — config is shared
  plain data, the handler is per-`r`.
- **Prove phase: handler per call.** Forced by the example, which builds a
  fresh handler env per prove (`Checked.purs:327-348`: `Ref` of the witness
  mask + `currentTransaction` per call):

```purescript
newtype BranchProver prevsSpec mpv prevsCarrier vkCarrier inputVal outputVal r =
  BranchProver
    ( AdviceHandler r
      -> StepInputs prevsSpec inputVal prevsCarrier vkCarrier
      -> Effect (Either ProveError (CompiledProof mpv (StatementIO inputVal outputVal)))
    )
```

`buildBranchProvers` needs no handler argument; the closure forwards it.

### `Pickles/Prove/Compile.purs`

```purescript
data RuleEntry ... r = RuleEntry
  { preComputeStepDomainLog2Fn :: AdviceHandler r -> StepProveContext ... -> Effect Int
  , stepCompileFn              :: AdviceHandler r -> StepProveContext ... -> Effect StepCompileResult
  , stepProveFn                :: AdviceHandler r -> StepProveContext ... -> StepCompileResult
                                  -> StepAdvice ... -> Effect (Either EvaluationError (StepProveResult outputSize))
  , slotVKs :: slotVKs
  }

compileMulti :: ... => AdviceHandler r -> CompileMultiConfig -> rulesCarrier
             -> Effect (MultiOutput ...)
```

Carrier element types in both class heads/instances change mechanically.
`runMultiProverBody`'s changes are localized to its two effectful seams
(`stepProveFn` / `wrapSolveAndProve` calls become `>>= case _ of Left e ->
pure (Left e); Right ... -> ...`). Expect noisy but mechanical diffs in the
RulesNil/RulesCons instance bodies' `@`-application chains.

### `Pickles/Prove/Step.purs`

```purescript
preComputeStepDomainLog2 :: ... => AdviceHandler r -> ctx -> rule -> Effect Int
stepCompile              :: ... => AdviceHandler r -> ctx -> rule -> Effect StepCompileResult
stepSolveAndProve        :: ... => AdviceHandler r -> ctx -> rule -> StepCompileResult
                              -> StepAdvice ... -> Effect (Either EvaluationError (StepProveResult outputSize))
```

The 3 `Except.throw` sites in `stepSolveAndProve` become `pure (Left
(WithContext ... e))` with manual `Either` plumbing (no transformer).
`liftExceptRow (runSolverT rawSolver unit)` (Step.purs:2161) →
`rawSolver handler unit`.

### `Pickles/Prove/Wrap.purs`

The wrap circuit emits no advice — **pin the wrap row to `()`** and drop `r`
from the wrap prove path:

```purescript
wrapCompile       :: ... => WrapCompileContext branches stepChunks -> Effect WrapCompileResult
wrapSolveAndProve :: ... => WrapProveContext branches mpv stepChunks slots
                  -> WrapCompileResult -> Effect (Either EvaluationError WrapProveResult)
```

(`Run.runBaseEffect` at Wrap.purs:405 disappears; internal solver runs with
`noAdvice`.)

## App handler conversion pattern

```purescript
-- BEFORE
runTransferM env = Run.runBaseEffect <<< Run.interpret
  (Run.on _merkle merkleH (Run.on _accountMap accountMapH (Run.on _transaction transactionH Run.send)))

-- AFTER  (per-effect handlers become F ~> Effect; chain ends in case_;
--         row loses its EFFECT component — the interpreter loops handle EFFECT)
runTransferM :: ... -> AdviceHandler (TransferAdvice d)
runTransferM env = AdviceHandler
  (on _merkle merkleH (on _accountMap accountMapH (on _transaction transactionH case_)))
```

The example's `TransferRow` (EFFECT-including) becomes dead — delete it.

## File-by-file order

**A. snarky core** (type-check after):
1. NEW `packages/snarky/src/Snarky/Backend/Advice.purs`
2. `packages/snarky/src/Snarky/Circuit/DSL/Monad.purs` (runAsProver loop, delete liftEffectRow)
3. `packages/snarky/src/Snarky/Circuit/DSL.purs` (re-exports)
4. `packages/snarky/src/Snarky/Backend/Builder.purs`
5. `packages/snarky/src/Snarky/Backend/Prover.purs`
6. `packages/snarky/src/Snarky/Backend/Compile.purs`

**B. snarky-dependent packages**:
- `snarky-kimchi/src/Snarky/Circuit/Kimchi/Utils.purs`:
  `verifyCircuitM :: AdviceHandler r -> ... -> Effect Unit`;
  `verifyCircuit = verifyCircuitM noAdvice`.
- `snarky-test-utils/src/Test/Snarky/Circuit/Utils.purs`: `runTest` uses
  `solver noAdvice`; `runTestM :: AdviceHandler r -> ...`; `circuitTestM'`
  replaces its natural-transformation param with
  `{ handler :: AdviceHandler r, beforeEach :: Effect Unit }` — **beforeEach
  must run per QuickCheck trial** (it replaces the `natWithReset`
  ledger/tree-reset pattern; run it inside `runScenarioM`'s per-sample loop).
- `snarky-test-utils/src/Test/Snarky/Circuit/Factors.purs`:
  `runFactor :: AdviceHandler (FACTOR f ())`.
- Handler-passing only: `snarky-test-utils/.../CheckedType.purs`,
  `snarky-kimchi/test/**` (Debugger, Proof, ProofCache, VarBaseMul),
  `merkle-tree/test/.../MerkleTree.purs` (`runMerkleRef ref ::
  AdviceHandler (MerkleRow ...)`; reset via beforeEach). merkle-tree *src*
  is untouched (it only defines the effect + circuits).

**C. pickles src**: `Prove/Step.purs`, `Prove/Wrap.purs`,
`Prove/Compile.purs` (RuleEntry, mkRuleEntry, BranchProver, both classes +
RulesNil/RulesCons instances, runMultiCompileFull, runMultiProverBody,
compileMulti; optionally re-export `noAdvice` from `Pickles`).

**D. pickles consumers** (two patterns: `Run.runBaseEffect $ compileMulti ...`
→ `compileMulti noAdvice ...`; `Run.runBaseEffect (RunExcept.runExcept
(prover {...}))` → `prover noAdvice {...}`, which already returns the
`Either` the tests case on): 11 test files under
`pickles/test/Test/Pickles/` (NoRecursionReturn, Chunks2, Chunks4, Codecs,
CompileValidation, SideLoadedMain, SimpleChain, SimpleChainN2,
TreeProofReturn, TwoPhaseChain, Sideload/DigestEqNrrSpec) +
`pickles-bench/src/{Compile,Prove}.purs`.

**E. example**:
- `Transaction/Monad.purs`: `runTransferM` / `runTransferCompileM` →
  `AdviceHandler (TransferAdvice d)`; delete `TransferRow`.
- `Transaction/MaskMonad.purs`: `runTransferMaskM` → `AdviceHandler ...`.
- `Transaction/Checked.purs` (`compileTxCircuit`): `compileMulti
  (runTransferMaskM { currentTransaction: Nothing, mask: maskRef }) cfg rules`
  in plain Effect; provers:
  `baseProver (runTransferMaskM { currentTransaction: Just env.tx, mask })
  {...} >>= either (throw <<< show) pure`. **`CompiledTx` is unchanged**, so
  `Env.purs`, `Snark/Worker.purs`, and the simulation need no edits.
- `test/Test/Snarky/Example/Circuits.purs`: handler + beforeEach for ledger
  reset; `compile runTransferCompileM ...` directly.

## Gotchas

- Unwrap `AdviceHandler` once outside each `tailRecM` loop.
- The prover loop passing the same handler into `runAsProver` is the rank-2
  point — it typechecks only via the newtype.
- Throw/ask semantics: loops hard-code "throw short-circuits" / "constant
  env" — verified safe (no `catch`/`local`/`catchAt`/`localAt` in the repo).
- After edits, grep touched files for leftover `unsafeCoerce` row-widening
  and dead `Run`/`Run.Except` imports (`--pedantic-packages --strict`
  catches the latter).
- Stack safety: all three loops are `tailRecM` in `Effect` — parity with the
  current Run-target loops.

## Verification

1. Per-phase type-check:
   `npx purs compile -g corefn $(npx spago sources -p <pkg> 2>/dev/null | grep -v '/test/') packages/<pkg>/test/**/*.purs --json-errors`
2. Tests in order: `npx spago test -p snarky`, `-p snarky-kimchi`,
   `-p merkle-tree`, `-p example`, then `-p pickles` (scope first with
   `-- --example "SimpleChain"`, then full).
3. `npx spago build --pedantic-packages --strict`.
4. Bench: `./tools/bench.sh`; compare against
   `bench-results/2131445f5-2026-06-11T22-30-54-362Z.json` (compile 6.54 s /
   prove 8.51 s steady-state) via `packages/pickles-bench/compare.mjs`.
   Optionally re-run the churn profiler (`prof/heap-churn-preload.mjs` +
   `prof/analyze_heapprofile.py`) and confirm the
   CatList/CatQueue/Control.Monad.Free slice collapses from 42–54%.
