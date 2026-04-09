# Wrap Main: advice monad refactor + OCaml alignment

An agentic loop for converting `Pickles.Wrap.Main.wrapMainCircuit` onto the
advice-monad pattern used by `Pickles.Step.Main.stepMain`, and aligning its
constraint system with the production `Wrap_main.wrap_main` by matching the
OCaml `exists` order exactly.

## Goal (what "done" looks like)

- `Pickles.Wrap.Main.wrapMainCircuit` has no `WrapMainAdvice` record. All
  private witness flows through `exists $ lift $ getXxx unit` calls against
  a `Pickles.Wrap.Advice.WrapWitnessM` instance, in OCaml `exists` order.
- The OCaml fixtures `wrap_main_circuit.json` and `wrap_main_n2_circuit.json`
  are regenerated from production `Wrap_main.wrap_main` (not the inlined
  `dump_circuit_impl.ml:wrap_main_circuit` stub).
- `npx spago test -p pickles-circuit-diffs` reports **0 diffs** for
  `wrap_main_circuit` and `wrap_main_n2_circuit`.
- `npx spago test -p pickles` still green (71/71 or better).
- `npx spago build --pedantic-packages --strict` reports 0 warnings, 0 errors.

## Prerequisites (run once, verify context before starting)

- [ ] Read `packages/pickles/src/Pickles/Step/Main.purs` end-to-end. This is
      the reference pattern.
- [ ] Read `packages/pickles/src/Pickles/Step/Advice.purs`. Structure of the
      new `WrapWitnessM` should mirror it.
- [ ] Read `packages/pickles/src/Pickles/Wrap/Main.purs` as it stands today.
      Identify every field on `WrapMainAdvice` / `WrapStatementData` /
      `UnfinalizedProofData` / `ProofWitnessData` / `OpeningProofData` /
      `MessagesData` — each one becomes either an `exists` call or a public
      input field.
- [ ] Read `mina/src/lib/crypto/pickles/wrap_main.ml` lines 138–578.
      Write down every `exists` call in order, with its `Req.*` name, its
      `Typ`, and the `with_label __LOC__` that surrounds it.
- [ ] Read `packages/pickles/CLAUDE.md`-style notes in `MEMORY.md`:
      "OCaml Right-to-Left Evaluation Order" and
      "Debugging with Variable Metadata".
- [ ] Confirm the build pipeline is green BEFORE starting:
  ```
  npx purs compile -g corefn $(npx spago sources -p pickles 2>/dev/null | grep -v '/test/') --json-errors 2>&1 | tail
  npx spago test -p pickles-circuit-diffs 2>&1 | tail
  npx spago test -p pickles 2>&1 | tail
  ```

## OCaml exists order (the truth — copy into code comments during step 3)

From `mina/src/lib/crypto/pickles/wrap_main.ml`:

1. `Req.Which_branch` (line 223) — `Field.typ` transported via `of_int`
2. *(in-circuit)* `One_hot_vector.of_index`, `Util.Wrap.ones_vector`,
   `Pseudo.choose domain_log2`, `Branch_data.Checked.Wrap.pack`,
   `Field.Assert.equal branch_data`
3. `Req.Proof_state` (line 267) — one structured `wrap_typ` over
   `Vector.init Max_proofs_verified.n Features.none` with
   `Shifted_value.Type2.wrap_typ Field.typ`. Contains
   `unfinalized_proofs : Vector mpv PerProofUnfinalized` +
   `messages_for_next_step_proof : Field.t`.
4. *(in-circuit)* `Wrap_verifier.choose_key which_branch step_keys`
   (constant lift — no exists) + feature flag consistency assertions.
5. `Req.Step_accs` (line 369) — `Vector.wrap_typ Inner_curve.typ Max_proofs_verified.n`
6. `Req.Old_bulletproof_challenges` (line 400) — heterogeneous
   `H1.Wrap_typ` over `Max_widths_by_slot.maxes`. For N1 the shape is
   `[N1; N0]`; for N2 it is `[N2; N1]`.
7. `Req.Evals` (line 415) — `Vector.wrap_typ (All_evals.wrap_typ Features.Full.none) Max_proofs_verified.n`
8. `Req.Wrap_domain_indices` (line 423) — `Vector.wrap_typ Field.typ Max_proofs_verified.n`
9. *(in-circuit)* `Vector.mapn [unfinalized_proofs; old_bp_chals; evals; wrap_domains]`
   **right-to-left**: per-proof sponge, `Wrap_hack.Checked.pad_challenges`,
   `Wrap_verifier.finalize_other_proof`, `Boolean.Assert.any [finalized; not should_finalize]`.
10. *(in-circuit)* `Vector.map2 prev_step_accs old_bp_chals` **right-to-left**
    running `hash_messages_for_next_wrap_proof`, then
    `Field.Assert.equal messages_for_next_step_proof prev_proof_state.messages_for_next_step_proof`.
11. `Req.Openings_proof` (line 531) — `Plonk_types.Openings.Bulletproof.wrap_typ`
    with `Type1` transport, `length = Tick.Rounds.n`.
12. `Req.Messages` (line 540) — `Plonk_types.Messages.wrap_typ Inner_curve.typ feature_flags`.
13. *(in-circuit)* `pack_statement Max_proofs_verified.n prev_statement` +
    `split_field` per Type1.
14. *(in-circuit)* `wrap_verify …` (IVP + 4 final assertions).

**Wrap statement IS a public input** (not an `exists`): the `main` function
takes `Wrap.Statement.In_circuit.t` via `~input_typ`. So in the PureScript
refactor the statement enters as a `WrapInputVar` parameter, not through
`WrapWitnessM`. Output is `Unit`. This is the key shape difference from
step_main (which has `Typ.unit` input and flat-output Vector).

## Phase 0 — OCaml fixture regeneration (run once, checkpoint before PS work)

The current fixture inlines `wrap_main_circuit` in `dump_circuit_impl.ml:2147`
and reads a flat input array. We need the fixture to come from production
`Wrap_main.wrap_main` instead.

### Step 0.1 — Replace `wrap_main_circuit` in `dump_circuit_impl.ml`

File: `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`

Find: `let wrap_main_circuit (inputs : Impls.Wrap.Field.t array) () =` (line ~2147)
and its N2 sibling (line ~2508).

Replace body with a call to `Wrap_main.wrap_main`. Use the same config
currently inlined: `branches = N1`, `step_widths = [N1]`,
`step_domains = [domain_log2 = 16]`, `feature_flags = Features.Full.none`,
`num_chunks = 1`, `step_keys = [dummy_step_vk]`. For N2: `step_widths = [N2]`
with `Max_widths_by_slot = [N2; N1]`.

Pattern to mirror: `Step_main_for_dump.step_main` invocation at
`dump_circuit_impl.ml:4438` and `:4592`. Install handlers for every `Req.*`
that return constant dummies — handlers are never actually run in
constraint-system-only mode, but the types must line up.

### Step 0.2 — Regenerate fixtures

```
nix develop mina#default -c bash -c 'cd mina && dune build ./src/lib/crypto/pickles/dump_circuit/dump_circuit.exe'
nix develop mina#default -c bash -c 'cd mina && dune exec ./src/lib/crypto/pickles/dump_circuit/dump_circuit.exe -- ../packages/pickles-circuit-diffs/circuits/ocaml/'
```

### Step 0.3 — Capture baseline diff

```
npx spago test -p pickles-circuit-diffs 2>&1 | tee /tmp/wrap-main-baseline.txt | grep -E "wrap_main|tests passed|tests failed"
```

Record:
- OCaml gate count for `wrap_main_circuit` and `wrap_main_n2_circuit`
  (from `packages/pickles-circuit-diffs/circuits/ocaml/wrap_main_*.json`).
- Current PS gate count (from `packages/pickles-circuit-diffs/circuits/results/wrap_main_*.json`).
- First diverging label (find via `varMetadata` + `placeVariables`, see
  `.claude/skills/kimchi-circuit-json-comparison/SKILL.md`).

**Exit condition:** OCaml fixtures exist, PS-vs-OC diff is captured in
`/tmp/wrap-main-baseline.txt`, you can name the first diverging gate.

## Phase 1 — New newtypes in `Pickles.Types` for wrap allocations

Goal: give `WrapWitnessM` structured return types whose `CircuitType`
instances already encode the OCaml `of_hlistable`/`Spec.pack` field order.

### Loop per newtype

For each of the new newtypes below:

1. **Define** the newtype record.
2. **Add a local `Tuple*` type alias** for the shape (only if the type is
   wide enough to benefit — follow the precedent of `FopProofStateTuple`,
   `StepPerProofWitnessTuple`, `PerProofUnfinalizedTuple`).
3. **Write the `CircuitType` instance** using
   `genericSizeInFields`/`genericValueToFields`/`genericFieldsToValue`/
   `genericVarToFields`/`genericFieldsToVar` delegated through the tuple.
4. **Write the `CheckedType` instance** (usually just `check (Ctor r) = check (tupleN r.field1 …)`).
5. **Verify with `purs compile -g corefn`** after each newtype before moving on.

### Newtypes to add

- **`WrapPrevProofState mpv sf f b`** — return type of `getWrapProofState`.
  Mirrors OCaml `Types.Step.Proof_state.wrap_typ` output.
  Fields:
  - `unfinalizedProofs :: Vector mpv (PerProofUnfinalized WrapIPARounds sf f b)`
  - `messagesForNextStepProof :: f`

  Tuple shape: `Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf f b)) f`.

- **`WrapOldBpChals slot0Width slot1Width f`** — return type of
  `getOldBulletproofChallenges`. Encodes `Max_widths_by_slot.maxes` as
  a pair of per-slot vectors.
  Fields:
  - `slot0 :: Vector slot0Width (Vector WrapIPARounds f)`
  - `slot1 :: Vector slot1Width (Vector WrapIPARounds f)`

  Tuple shape: `Tuple2 (Vector slot0Width (Vector WrapIPARounds f)) (Vector slot1Width (Vector WrapIPARounds f))`.

  **Open question:** does production OCaml allocate slot 0 before slot 1,
  or the reverse? Verify by reading `H1.Wrap_typ` expansion in
  `wrap_main.ml:372-404` and grepping for `Max_widths_by_slot.length`.
  Add a doc comment recording the answer.

- **`WrapEvalsVec mpv a`** (optional — may just reuse `Vector mpv (StepAllEvals a)`
  directly if `StepAllEvals`'s `CircuitType` matches OCaml's
  `All_evals.wrap_typ` exactly). Compare field order of `StepAllEvals`
  (`publicEvals`, `witnessEvals`, `coeffEvals`, `zEvals`, `sigmaEvals`,
  `indexEvals`, `ftEval1`) against `Plonk_types.All_evals.In_circuit.t`'s
  `of_hlistable` — if they agree, skip this newtype.

### Checkpoint

- [ ] `npx purs compile -g corefn $(npx spago sources -p pickles 2>/dev/null | grep -v '/test/') --json-errors 2>&1 | tail` reports 0 errors.
- [ ] All new newtypes exported from `Pickles.Types`.

## Phase 2 — Rewrite `Pickles.Wrap.Advice`

### Step 2.1 — New class head

```purescript
class
  ( Monad m
  , WeierstrassCurve f g
  ) <=
  WrapWitnessM (branches :: Int) (mpv :: Int) (slot0Width :: Int) (slot1Width :: Int) g f m
  | g -> f where
```

Drop the existing `ds`/`dw` params (hardcode `StepIPARounds` / `WrapIPARounds`
in method signatures — they're not actually polymorphic, same lesson as
step_main).

### Step 2.2 — Method list (one per OCaml `Req.*`, in OCaml exists order)

1. `getWhichBranch :: Unit -> m (F f)`
2. `getWrapProofState :: Unit -> m (WrapPrevProofState mpv (Type2 (F f)) (F f) Boolean)`
3. `getStepAccs :: Unit -> m (Vector mpv (WeierstrassAffinePoint g (F f)))`
4. `getOldBulletproofChallenges :: Unit -> m (WrapOldBpChals slot0Width slot1Width (F f))`
5. `getEvals :: Unit -> m (Vector mpv (StepAllEvals (F f)))`
6. `getWrapDomainIndices :: Unit -> m (Vector mpv (F f))`
7. `getOpeningProof :: Unit -> m (WrapProofOpening (WeierstrassAffinePoint g (F f)) (Type1 (F f)))`
8. `getMessages :: Unit -> m (WrapProofMessages (WeierstrassAffinePoint g (F f)))`

### Step 2.3 — `Effect` instance

```purescript
instance
  ( WeierstrassCurve f g
  , Reflectable branches Int
  , Reflectable mpv Int
  , Reflectable slot0Width Int
  , Reflectable slot1Width Int
  ) =>
  WrapWitnessM branches mpv slot0Width slot1Width g f Effect where
  getWhichBranch _ = throw "impossible! getWhichBranch called during compilation"
  -- ... all methods throw
```

### Step 2.4 — Delete old methods

Remove `getStepIOFields`, the old `getEvals` / `getMessages` / `getOpeningProof`
/ `getUnfinalizedProofs` / `getStepAccs` / `getOldBpChallenges` if their
signatures change. Update any callers in `Pickles.Wrap.Circuit` (the smaller
sub-circuit) — it may need its own separate wrap-lite advice class, or it
can share this one if the types line up.

### Checkpoint

- [ ] `npx purs compile -g corefn $(npx spago sources -p pickles 2>/dev/null | grep -v '/test/') --json-errors 2>&1 | tail` reports 0 errors (or only the expected errors in `wrapMainCircuit` / `wrapCircuit` which get fixed in Phase 3/4).

## Phase 3 — Rewrite `wrapMainCircuit`

File: `packages/pickles/src/Pickles/Wrap/Main.purs`

### Step 3.1 — New signature

```purescript
wrapMain
  :: forall @branches @slot0Width @slot1Width _branchesPred t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => WrapWitnessM branches MaxProofsVerified slot0Width slot1Width VestaG WrapField m
  => Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Add 1 _branchesPred branches
  => WrapMainConfig branches
  -> WrapInputVar WrapIPARounds   -- the public-input wrap statement (from Pickles.Wrap.Circuit)
  -> Snarky (KimchiConstraint WrapField) t m Unit
```

Key shape points:
- Input is a `WrapInputVar` (the public-input wrap statement), not Unit.
- Output is `Unit`. Wrap_main asserts — it does not produce a flat output Vector.
- Drop all the `WrapMainAdvice` and `WrapStatementData` type parameters.

### Step 3.2 — Body (strict OCaml order, each step matches a numbered item in "OCaml exists order" above)

For each `exists $ lift $ get… unit` call, wrap in `label "..."` matching
OCaml's `with_label __LOC__` for the same line.

```
wrapMain config stmt = do
  -- 1. Req.Which_branch
  whichBranchField <- label "which-branch" $
    exists $ lift $ getWhichBranch unit

  -- 2. In-circuit derivation (existing block1 logic, reading from whichBranchField
  --    instead of advice.whichBranch)
  whichBranch <- Pseudo.oneHotVector @branches whichBranchField
  firstZero <- Pseudo.choose whichBranch config.stepWidths (\w -> const_ (fromInt w))
  { maskVal0, maskVal1 } <- ... (ones_vector logic)
  domainLog2 <- Pseudo.choose whichBranch config.domainLog2s (\d -> const_ (fromInt d))
  label "branch-data-assert" $ assertEqual_ stmt.branchData (packBranchData maskVal0 maskVal1 domainLog2)

  -- 3. Req.Proof_state
  WrapPrevProofState pps <- label "proof-state" $
    exists $ lift $ getWrapProofState unit
  let { unfinalizedProofs, messagesForNextStepProof: prevMsgForNextStep } = pps

  -- 4. chooseKey + feature flag consistency (existing block2)
  chosenVK <- chooseKey whichBranch config.stepKeys
  let { chosenSigmaCommLast, chosenColumnComms } = ...

  -- 5. Req.Step_accs
  stepAccs <- label "step-accs" $
    exists $ lift $ getStepAccs unit

  -- 6. Req.Old_bulletproof_challenges
  WrapOldBpChals oldBpChals <- label "old-bp-chals" $
    exists $ lift $ getOldBulletproofChallenges unit

  -- 7. Req.Evals (inside "new-bp-chals" label)
  newBpChals <- label "new-bp-chals" do
    evals <- exists $ lift $ getEvals unit

    -- 8. Req.Wrap_domain_indices
    wrapDomainIndices <- exists $ lift $ getWrapDomainIndices unit

    -- 9. FOP loop: Vector.mapn RIGHT-TO-LEFT (proof mpv-1 first, then mpv-2, ..., then 0)
    --    Match OCaml by doing `for (Vector.reverse zipped)` then `Vector.reverse` the result.
    forReverseOrder unfinalizedProofs oldBpChals evals wrapDomainIndices \unf bpc ev wdi -> do
      -- sponge from sponge_digest_before_evaluations
      -- pad_challenges bpc
      -- wrapFinalizeOtherProofCircuit ...
      -- assertAny_ [finalized; not shouldFinalize]
      pure expandedChallenges

  -- 10. Message hash loop: Vector.map2 prev_step_accs old_bp_chals RIGHT-TO-LEFT
  prevMsgForNextWrap <- forReverseOrder stepAccs oldBpChals \acc bpc ->
    hashMessagesForNextWrapProofCircuit' { sg: acc, allChallenges: bpc }
  label "assert-msg-step" $ assertEqual_ stmt.messagesForNextStepProof prevMsgForNextStep

  -- 11. Req.Openings_proof
  openingProof <- label "openings-proof" $
    exists $ lift $ getOpeningProof unit

  -- 12. Req.Messages
  messages <- label "messages" $
    exists $ lift $ getMessages unit

  -- 13. pack_statement + split_field (existing block5 logic)
  let publicInput = buildPublicInput unfinalizedProofs prevMsgForNextStep prevMsgForNextWrap

  -- 14. wrapVerify (existing block6 logic)
  wrapVerify ivpParams fullIvpInput verifyInput
```

### Step 3.3 — Delete dead types

Once the new body compiles:
- `WrapMainAdvice`
- `UnfinalizedProofData`
- `ProofWitnessData`
- `OpeningProofData`
- `MessagesData`
- `WrapStatementData` (if fully subsumed by `WrapInputVar`)

### Checkpoint

- [ ] `npx purs compile -g corefn $(npx spago sources -p pickles 2>/dev/null | grep -v '/test/') --json-errors 2>&1 | tail` reports 0 errors.

## Phase 4 — Update the test wrappers

Files:
- `packages/pickles-circuit-diffs/src/Pickles/CircuitDiffs/PureScript/WrapMain.purs`
- `packages/pickles-circuit-diffs/src/Pickles/CircuitDiffs/PureScript/WrapMainN2.purs`

### Step 4.1 — Drop public-input parsing

Remove `parseUnfinalizedProof`, `parseEvals`, and any `fieldsToValue`-based
advice construction. These wrappers become thin specializations like
`compileStepMainSimpleChain`:

```purescript
compileWrapMainN1 :: WrapMainSrsData -> CompiledCircuit WrapField
compileWrapMainN1 params =
  compileWrapMain @1 @1 @0 config dummyWrapStatement
```

### Step 4.2 — `compileWrapMain` entry point

Add to `Pickles.Wrap.Main`:

```purescript
compileWrapMain
  :: forall @branches @slot0Width @slot1Width _branchesPred
   . Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Add 1 _branchesPred branches
  => WrapMainConfig branches
  -> WrapInput WrapIPARounds   -- constant wrap-statement value for the dummy proof-state input
  -> CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
compileWrapMain config dummyStmt = unsafePerformEffect $
  compile
    (Proxy @(WrapInput WrapIPARounds))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (wrapMain config)
    Kimchi.initialState
```

### Checkpoint

- [ ] `npx purs compile -g corefn $(npx spago sources -p pickles-circuit-diffs 2>/dev/null | grep -v '/test/') --json-errors 2>&1 | tail` reports 0 errors.

## Phase 5 — Test infrastructure

File: `packages/pickles/test/Test/Pickles/TestContext.purs`

### Step 5.1 — Add `WrapProverM` advice env

Mirror `StepProverM`:

```purescript
type WrapAdvice branches mpv slot0Width slot1Width f =
  { whichBranch :: F f
  , wrapProofState :: WrapPrevProofState mpv (Type2 (F f)) (F f) Boolean
  , stepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F f))
  , oldBpChals :: WrapOldBpChals slot0Width slot1Width (F f)
  , evals :: Vector mpv (StepAllEvals (F f))
  , wrapDomainIndices :: Vector mpv (F f)
  , openingProof :: WrapProofOpening (WeierstrassAffinePoint VestaG (F f)) (Type1 (F f))
  , messages :: WrapProofMessages (WeierstrassAffinePoint VestaG (F f))
  }

newtype WrapProverM branches mpv slot0Width slot1Width f a =
  WrapProverM (ReaderT (WrapAdvice branches mpv slot0Width slot1Width f) Effect a)

instance WrapWitnessM branches mpv slot0Width slot1Width VestaG WrapField (WrapProverM branches mpv slot0Width slot1Width WrapField) where
  getWhichBranch _ = WrapProverM $ map _.whichBranch ask
  getWrapProofState _ = WrapProverM $ map _.wrapProofState ask
  -- ... etc
```

For the circuit-diffs tests (compilation-only), a placeholder throw
instance is enough — the real env only matters when we start actually
proving wrap.

### Checkpoint

- [ ] `npx purs compile -g corefn $(npx spago sources -p pickles 2>/dev/null | grep -v '/test/') packages/pickles/test/**/*.purs --json-errors 2>&1 | tail` reports 0 errors.

## Phase 6 — Diff convergence loop

This is the iterative part. After Phase 0–5 everything compiles, but the
constraint system will not yet match the regenerated OCaml fixture exactly.

### Loop: until `npx spago test -p pickles-circuit-diffs` reports
      `wrap_main_circuit matches OCaml` AND
      `wrap_main_n2_circuit matches OCaml`

1. **Run the test**, capture output to `/tmp/wrap-main-diff.txt`.
   ```
   npx spago test -p pickles-circuit-diffs 2>&1 | tee /tmp/wrap-main-diff.txt | grep -E "wrap_main|tests passed|tests failed"
   ```

2. **Compare gate counts** (PS side vs OCaml side):
   ```
   cat packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json | python3 -c "
   import json,sys
   d = json.load(sys.stdin)
   print('PS gates:', len(d['purescript']['gates']))
   print('OC gates:', len(d['ocaml']['gates']))
   print('PS cachedConstants:', len(d['purescript']['cachedConstants']))
   print('OC cachedConstants:', len(d['ocaml']['cachedConstants']))
   "
   ```

3. **Find first diverging gate** via structural walk (normalize out
   `variables` metadata):
   ```
   cat packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json | python3 -c "
   import json,sys
   d = json.load(sys.stdin)
   def norm(g): return {'kind': g['kind'], 'coeffs': g['coeffs'], 'wires': g['wires']}
   ps = [norm(g) for g in d['purescript']['gates']]
   oc = [norm(g) for g in d['ocaml']['gates']]
   for i,(p,o) in enumerate(zip(ps,oc)):
       if p != o:
           print('First diff at row', i)
           print('PS:', p)
           print('OC:', o)
           break
   "
   ```

4. **Map diverging row back to a label** using
   `placeVariables` / `varMetadata` (see
   `.claude/skills/kimchi-circuit-json-comparison/SKILL.md` "Debugging with
   Variable Metadata").

5. **Diagnose** the label → find the corresponding `label "..."` block in
   `Pickles.Wrap.Main.wrapMain` → cross-reference with `wrap_main.ml`.
   Common failure modes (in order of likelihood):
   - **Wrong `exists` order**: allocation happens before a sibling
     allocation it should follow. Fix: reorder the `exists` calls to match
     OCaml numbered order (§ "OCaml exists order" above).
   - **Left-to-right vs right-to-left loop**: `Vector.mapn` / `Vector.map2`
     in OCaml evaluate right-to-left. Fix: traverse
     `Vector.reverse input` and `Vector.reverse` the result. See
     `MEMORY.md` "OCaml Right-to-Left Evaluation Order".
   - **`equals_` argument order swapped**: OCaml's `equal a b` and PS's
     `equals_ b a` produce different R1CS coefficients. Fix: match OCaml
     argument order literally.
   - **Type1 vs Type2 shift**: wrong `Shifted_value.Type*` representation
     for a deferred value. Fix: check `wrap_main.ml`'s destructure at
     line 175–219 for which fields are Type1 vs Type2.
   - **`assert_16_bits` on/off for `Req.Proof_state`**: OCaml production
     uses `assert_16_bits`, but our current `UnChecked` wrapper suppresses
     the check. If the regenerated fixture includes these constraints,
     drop the `UnChecked` wrapper on the unfinalized challenges. If the
     domain blows past 2^15, fix by enabling the check (this is a real
     constraint count increase, not a layout bug).
   - **Off-by-one on slot widths** in `WrapOldBpChals`: slot 0 allocated
     before slot 1 vs the reverse. Check `H1.Wrap_typ` expansion order.
   - **Feature-flag consistency assertions**: if OCaml emits them but PS
     skips, the row count diverges by ~14 constant rows. For `Features.none`
     these are all `Boolean.Assert.(=) Boolean.false_ Boolean.false_` → a
     predictable constant-gate pattern. Add them in OCaml order.

6. **Make the smallest possible fix**, re-run, loop.

### Exit condition

- [ ] `npx spago test -p pickles-circuit-diffs 2>&1 | grep "wrap_main_circuit matches OCaml"` prints a match.
- [ ] `npx spago test -p pickles-circuit-diffs 2>&1 | grep "wrap_main_n2_circuit matches OCaml"` prints a match.
- [ ] Total tests: 74/74 (or higher if new fixtures were added).

## Phase 7 — Green the rest of the build

### Step 7.1 — Pickles test suite

```
npx spago test -p pickles 2>&1 | tail
```

Expect 71/71. If a test broke because `wrapCircuit` (the sub-circuit in
`Pickles.Wrap.Circuit`) still uses the old `WrapWitnessM` method shape,
either:
- Update `wrapCircuit` to match the new class, OR
- Introduce a smaller `class WrapSubCircuitWitnessM` for the sub-circuit
  and keep `WrapWitnessM` exclusively for top-level wrap_main. The former
  is simpler; the latter preserves the existing test surface.

### Step 7.2 — Strict build

```
npx spago build --pedantic-packages --strict 2>&1 | grep -E "Warnings|Errors"
```

Expect `0 0 0` on both lines.

### Step 7.3 — Update `FOLLOW-UPS.md`

Remove or cross out:
- `TODO(wrap_main_advice)` — the main item (line 18).
- "FOP domain as separate argument" (line 43) — if Phase 3 refactor folded
  the per-proof domain into the advice struct.
- "Abstract ones_vector" (line 47) — if Phase 3 extracted it.

If any of those remain in a partial state, leave them but update the
description to reflect what was done and what's left.

### Step 7.4 — Update `MEMORY.md`

Add a short entry under "Pickles" summarizing:
- New shape of `WrapWitnessM` (branches, mpv, slot0, slot1, g, f) with
  fundep `g -> f`.
- Key OCaml-order pitfalls encountered during Phase 6 (if any were
  non-obvious and not already documented in the right-to-left memory).
- Any new newtype in `Pickles.Types`.

## Risks and open questions (decide at start of Phase 0, not mid-loop)

- [ ] **Does the OCaml dump handler for `Req.Step_accs` / `Req.Openings_proof` /
      `Req.Messages` need real curve points, or will `Inner_curve.Params.one`
      dummies do?** In constraint-system-only mode the handlers are never
      invoked, so any well-typed value should work. Verify by inspecting how
      `Step_main_for_dump.step_main` is called in `dump_circuit_impl.ml:4438`.

- [ ] **Is `Wrap_main.wrap_main` a functor or a plain function?** This
      determines whether we need a `Wrap_main_for_dump = Wrap_main.Make(...)`
      or can call `Wrap_main.wrap_main` directly. Grep for
      `let wrap_main` / `module Wrap_main` in `mina/src/lib/crypto/pickles/wrap_main.ml`.

- [ ] **Does the `WrapStatement` public-input CircuitType match OCaml's
      `Wrap.Statement.In_circuit.typ` field order?** If not, every public
      input row is off. Compare `Pickles.Types.WrapStatement` field order
      against `wrap_main.ml:175-219`'s destructure.

- [ ] **`WrapOldBpChals` slot allocation order.** Inspect the `H1.Wrap_typ`
      expansion at `wrap_main.ml:372-404`. Does slot 0 allocate first or
      slot 1? Write the answer in the newtype doc.

- [ ] **`Features.none` vs real feature flags in the fixture.** The current
      inlined fixture hardcodes `Features.Full.none`. When switching to
      production `Wrap_main.wrap_main`, we must call it with the same
      `feature_flags` config so the resulting circuit remains diff-comparable.
      Verify the dump driver passes `Features.Full.none`.

## Notes for the agent running this loop

- **Do not batch refactors across phases**. If Phase 2 is mid-flight and
  Phase 3 looks tempting, stop — Phase 3 requires Phase 2 to typecheck
  first, otherwise the Phase 3 diff will be unreadable.
- **Always re-run `purs compile -g corefn` after every file edit**. Never
  let a compile error sit while you edit another file.
- **Keep the diff loop tight**. One behavior change per iteration. If you
  make two changes and the diff gets worse in a way you can't localize,
  revert one and try again.
- **Never mark a phase complete without running its checkpoint commands**.
  Compiling is not the same as passing tests; passing one test is not the
  same as passing all tests.
- **When stuck on a diff**: don't guess. Use `label` to mark the suspected
  block, rebuild, locate the label in the resulting gate metadata, and
  walk OCaml's corresponding code literally. Most diffs are off-by-one
  ordering bugs, not semantic bugs.
