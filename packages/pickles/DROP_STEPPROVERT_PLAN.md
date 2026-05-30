# Refactor: delete StepProverT, witness monad = bare `m`

Branch `pickles-drop-stepprovert` (off `example-sign-transfer`, HEAD ee4239c2). GOAL: pickles stops defining its own prover transformer. Witness/advice monad becomes the caller's bare `m` (MonadEffect). Then app advice (`MerkleRequestM`/`AccountMapM`) are ordinary instances on the app monad → NO orphan, NO StepProverT stacking, NO lift-depth, NO `CircuitM` reparam. Keeps ee4239c2's `m`-threading skeleton (RuleEntry/compileMulti carry `m`).

## Core mechanism
`StepProverT … m = ReaderT StepAdvice (StateT StepProverCapture m)` is DELETED. Its two layers split:
- **ReaderT advice → pure argument.** `stepMain` takes `advice :: StepAdvice …` as a plain arg.
- **StateT capture → one contained `Ref (Maybe (Array (FVar StepField)))`.** Passed into `stepMain` (solver makes the whole return public, so capture cannot be a pure return → `Ref` is the only non-public channel; it's a value, not a transformer, so app advice still resolves on bare `m`).

## The deferral invariant (LOAD-BEARING)
Every advice read today is `exists $ lift (getX unit)`; the `m`-action defers the read so COMPILE (which discards the `exists` body) never forces it. Replacement MUST preserve this via the FUNCTOR, not eager projection:
- `exists $ lift (getStepPublicInput unit)`  →  `exists (pure advice <#> \(StepAdvice r) -> r.publicInput)`
- `pure advice` does NOT force `advice` (closure-captured); the projection runs only when the AsProverT body runs (prove). At compile, dummy advice (`unsafeCoerce unit`) is WHNF-eval'd by `pure` but never projected. NEVER write `exists (pure advice.field)` (eager → crashes on dummy at compile).

## Rule API change (kills StepRuleM + the rank-2 wall)
Rule body's only advice use is `getPrevAppStates`. New `StepRule` takes a deferred getter arg instead:
```
type StepRule n valCarrier inputVal input outputVal output prevInputVal prevInput =
  forall t m. CircuitM StepField (KimchiConstraint StepField) t m => MonadEffect m
  => CircuitType … (×3) => CheckedType …
  => AsProverT StepField m valCarrier   -- deferred prev-states getter
  -> input
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput n prevInput output)
```
Drops `StepWitnessM/StepSlotsM/StepPrevValuesM/StepUserOutputM` constraints. App rules are then just `… => MerkleRequestM m => AccountMapM m => <StepRule shape>` — plain constraints on bare `m`, dischargeable at the concrete app monad. **`StepRuleM` and `mkRuleEntryM` are DELETED** (no concrete-advice-monad form needed). Rule body change, e.g. TreeProofReturn:
```
treeProofReturnRule getPrevStates _ = do
  nrrInput  <- exists $ getPrevStates <#> \(StatementIO {output:nrrOut} /\ _) -> nrrOut
  prevInput <- exists $ getPrevStates <#> \(_ /\ StatementIO {output:prevOut} /\ _) -> prevOut
  ...
```
`stepMain` builds `getPrevStates = pure advice <#> \(StepAdvice r) -> r.prevAppStates` and calls `rule getPrevStates publicInput`.

## DELETE list (Pickles.Prove.Step + Pickles.Step.Advice)
- `StepProverT` newtype + all derived/advice instances (StepWitnessM/StepSlotsM/StepPrevValuesM/StepUserOutputM/SideloadedVKsM on StepProverT), `runStepProverT`, `StepProverCapture`, `initialStepProverCapture`, `StepRuleM`.
- `Pickles.Step.Advice` classes `StepWitnessM/StepSlotsM/StepPrevValuesM/StepUserOutputM` + their Effect throw instances + methods. KEEP nothing (advice is now record projection). Likely delete the whole module; check `SideloadedVKsM` (Pickles.Sideload.Advice) usage — stepSolveAndProve already pulls `sideloadedVKs` straight from the StepAdvice field, so the in-rule `getSideloadedVKsCarrier` is likely dead.
- KEEP `StepAdvice` record (it's the data, now passed by value) + `buildStepAdvice`.

## `stepMain` (Pickles.Step.Main) changes
- Drop `StepWitnessM/StepSlotsM/StepPrevValuesM/StepUserOutputM` constraints; keep `CircuitM`,`MonadEffect m`.
- New params: `advice :: StepAdvice …` and `captureRef :: Ref (Maybe (Array (FVar StepField)))`.
- Each `exists $ lift (getX @… unit)` → `exists (pure advice <#> \(StepAdvice r) -> r.FIELD)`. Field map:
  getStepPublicInput→publicInput; getWrapVerifierIndex→wrapVerifierIndex; getStepSlotsCarrier→perProofSlotsCarrier; getStepUnfinalizedProofs→publicUnfinalizedProofs; getMessagesForNextWrapProof→messagesForNextWrapProof; getMessagesForNextWrapProofDummyHash→messagesForNextWrapProofDummyHash.
- `rule publicInput` → `rule (pure advice <#> \(StepAdvice r) -> r.prevAppStates) publicInput`.
- Capture block: `_ <- exists $ lift do { liftEffect (Ref.write captureRef (Just publicOutputFields)); pure unit }` (lift = AsProverT MonadTrans; inner `m Unit`, m MonadEffect). publicOutputFields already computed at line 898.

## Runner changes (the three functions in Pickles.Prove.Step)
- `stepCompile`/`preComputeStepDomainLog2`: run `stepMain dummyAdvice throwawayRef …` in bare `m` (was `runStepProverT dummyAdvice …`). dummyAdvice = `unsafeCoerce unit`; throwawayRef via `liftEffect (Ref.new Nothing)` (compile skips exists → never written). Just `runSolverT solver unit` in `m` (no StepProverT unwrap). Rule param type → new `StepRule`.
- `stepSolveAndProve`: `captureRef <- liftEffect (Ref.new Nothing)`; build solver running `stepMain advice captureRef …` in bare `m`; `eRes <- lift (runSolverT rawSolver unit)` (NO runStepProverT, NO StateT tuple); `captured <- liftEffect (Ref.read captureRef)`; same post-solve FVar eval (`Nothing` → FailedAssertion). Rule param type → new `StepRule`.

## Compile.purs changes
- DELETE `mkRuleEntryM`. `mkRuleEntry`: drop the `StepRuleM` annotated `ruleCompile`/`ruleProve` locals (pass `rule` straight through — it's the new `StepRule`); drop StepWitnessM/StepSlotsM/StepPrevValuesM/StepUserOutputM from the constraint set (no longer referenced). `RuleEntry`'s `stepCompileFn`/`stepProveFn` rule param types → new StepRule. Keep the `m` param everywhere.
- `CompilableRulesSpecShape`/Cons: drop now-unused advice-class constraints if any.

## Consumers
- 12 rules + their tests: signature gains the getter arg; `getPrevAppStates unit` → project the getter (see TreeProofReturn above). Rules with no prevs (NRR, mpv=0) just ignore the getter (`_`).
- `Pickles.purs` exports: drop `StepProverT`(if exported), `StepRuleM`, `mkRuleEntryM`, `getPrevAppStates`, `StepRule` re-export stays.

## Validation gates (byte-EXACT — representational change only)
1. `npx purs compile -g corefn $(npx spago sources -p pickles | grep -v /test/) --json-errors` → 0.
2. Fast: `Test.Pickles.Prove.CompileValidation` (compile-only).
3. Proving: SimpleChain + TreeProofReturn prove+verify; witnesses must stay byte-identical (this is a representational refactor — values unchanged). Use the proof cache / KIMCHI_WITNESS_DUMP if drift suspected.
4. Then example txn app: app advice resolves on bare AppM with a single `lift`; build base+merge rules (no StepRuleM).

## Node: `nvm use 23`. Type-check loop excludes other pkgs' test files.
