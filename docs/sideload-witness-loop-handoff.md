# Side-loaded witness diff loop — handoff doc

Self-contained brief for a fresh Claude session. After `/clear`, point me
at this file: "read `docs/sideload-witness-loop-handoff.md` and proceed
with M6."

## Goal

Drive PS to byte-equality with OCaml on the side-loaded `step_main`
witness (counter 2 of `dump_side_loaded_main.exe`) by iterating
`tools/witness_diff.sh` against the committed golden dumps.

CS is already byte-identical (commit `a4717546`); any divergence on
witnesses must be in advice values, not the circuit shape.

## Where the work stands

Done and committed (M1-M5):

- **OCaml dumps** (`mina` submodule + parent commits `1bbfc172`,
  `ab1d0335`):
  - 4 OCaml witness goldens at
    `packages/pickles/test/fixtures/witness_sideload/`
    (counters 0..3, generated with `KIMCHI_DETERMINISTIC_SEED=42`).
  - 4 OCaml side-loaded VK + wrap proof + statement + wrapping JSON
    fixtures at `packages/pickles/test/fixtures/sideload_main_child/`
    (vk.serde.json, proof.serde.json, statement.json, wrapping.json
    + README) — produced from the SAME OCaml run.
  - `dump_side_loaded_main.ml` extended with `dump_child_fixture ()`
    gated on `SIDELOAD_FIXTURE_DIR` env var.
- **PS loader** (commit `c59c0495`):
  - `Test.Pickles.Sideload.RoundTripMainChildSpec` — verifies
    `loadNrrFixture` parses the new fixture; VK byte-round-trips.
  - `Test.Pickles.Sideload.Loader.decodeInt64` extended to handle
    medium-sized JSON ints (between ±2^31 and ±2^53). Latent bug —
    landed as part of M5.
  - All 4 sideload specs pass.

Pending (M6-M11):

- **M6** (next): make `compileMulti` type-check + return
  `BranchProver` for a `PrevsSpecSideLoadedCons` spec.
- M7: drive one parent step prove (no env vars yet, just confirm
  end-to-end runs without crash).
- M8: same with `KIMCHI_DETERMINISTIC_SEED=42 KIMCHI_WITNESS_DUMP=...`
  → produce `/tmp/ps_sl_0.txt`.
- M9: first witness diff via `tools/witness_diff.sh` against
  `packages/pickles/test/fixtures/witness_sideload/ocaml_main_step_b1.txt`
  — find first `(col, row)` mismatch.
- M10..M∞: fix → re-run → re-diff loop.
- M11: counter 3 (parent wrap proof).

## M6 — exact plan (the architectural decision)

**Reuse the existing step advice monad** — `StepProverT` already
exists in `Pickles.Prove.Step.purs:1753`. The runtime side-loaded VK
plumbs through `StepAdvice` (the `Reader` payload of `StepProverT`),
just like every other piece of prove-time advice. NO new monad, NO
parameter to `BranchProver`, NO m-polymorphism refactor.

Three pieces:

### Piece 1: extend `StepAdvice` with a `sideloadedVKs` field

`Pickles.Prove.Step.purs:1683`:

```purescript
newtype StepAdvice prevsSpec ds dw inputVal len carrier valCarrier vkCarrier =
  StepAdvice
    { perProofSlotsCarrier :: carrier
    , publicInput :: inputVal
    , publicUnfinalizedProofs :: Vector len (PerProofUnfinalized ...)
    , messagesForNextWrapProof :: Vector len (F StepField)
    , messagesForNextWrapProofDummyHash :: F StepField
    , wrapVerifierIndex :: VerificationKey ...
    , kimchiPrevChallenges :: Vector len { sgX, sgY, challenges }
    , prevAppStates :: valCarrier
    , sideloadedVKs :: vkCarrier      -- NEW field
    }
```

Adds a new type parameter `vkCarrier` to `StepAdvice`. Ripple this
through every reference site.

### Piece 2: populate `sideloadedVKs` in `mkStepAdvice`

`Pickles.Prove.Compile.purs` — three instance bodies:

- `PrevsSpecNil`: `sideloadedVKs = unit` (and ripple unit through the
  recursion's accumulator).
- `PrevsSpecCons` (around line 1122): `sideloadedVKs = unit /\
  restAdv.sideloadedVKs`.
- `PrevsSpecSideLoadedCons` (around line 1633): `sideloadedVKs =
  headVk /\ restAdv.sideloadedVKs`. The `headVk` is already
  destructured at line 1633 — just persist it.

### Piece 3: add `SideloadedVKsM` instance for `StepProverT`

`Pickles.Prove.Step.purs` (near other StepProverT instances around
line 1820):

```purescript
instance
  ( Monad m
  , SideloadedVKsCarrier prevsSpec vkCarrier
  ) =>
  SideloadedVKsM
    prevsSpec
    (StepProverT prevsSpec ds dw inputVal len carrier valCarrier vkCarrier m)
    vkCarrier
  where
  getSideloadedVKsCarrier _ =
    StepProverT $ map (\(StepAdvice r) -> r.sideloadedVKs) ask
```

Then in `stepSolveAndProve` (around line 2190), replace:

```purescript
sideloadedCarrier <- lift $ getSideloadedVKsCarrier @prevsSpec unit
```

with reading directly from the already-passed `StepAdvice`:

```purescript
sideloadedCarrier <- pure adv.sideloadedVKs
```

(or just `let sideloadedCarrier = adv.sideloadedVKs`.)

### Piece 4 (compile-time): add missing `MkUnitVkCarrier` instance

`Pickles.Sideload.Advice.purs:144` (compile-time path — values
discarded by `exists ~compute:` at compile, only SHAPE matters):

```purescript
instance
  MkUnitVkCarrier rest =>
  MkUnitVkCarrier (Sideload.VerificationKey /\ rest) where
  mkUnitVkCarrier = Sideload.dummy /\ mkUnitVkCarrier
```

This makes compile-time call sites (`stepCompile`,
`preComputeStepDomainLog2` in `Pickles.Prove.Step`) work for
side-loaded specs via the existing Effect-based `SideloadedVKsM`
instance. Only the SHAPE matters at compile; values discarded.

## Why this is the right design (vs alternatives discussed)

- **NOT option A (vkCarrier on RuleEntry)**: would pin the VK to
  compile-time, contradicting OCaml's per-prove `~handler` model.
  Wrong in production (Mina-style DB-lookup-per-prove can't bind at
  compile).
- **NOT option B (m-polymorphic refactor)**: invasive — touches
  `compileMulti`, `runMultiProverBody`, three Step.purs functions,
  every test's BranchProver invocation. Not necessary because
  StepProverT already exists.
- **NOT option D (vkCarrier as StepInputs param)**: also wrong —
  bypasses the existing advice-typeclass architecture. PS's
  StepWitnessM/StepSlotsM/etc are typeclass-driven; vkCarrier should
  be too.
- **YES this approach (reuse StepAdvice)**: matches OCaml advice
  semantics, matches PS's existing advice-typeclass pattern, single
  new field + single new instance, no signature changes elsewhere.

## File references the implementation needs

- `packages/pickles/src/Pickles/Prove/Step.purs`
  - `1683` — `StepAdvice` newtype
  - `1753` — `StepProverT` newtype
  - `1820` — `StepSlotsM` instance for StepProverT (template for new
    `SideloadedVKsM` instance)
  - `1934` — `stepCompile` (Effect-typed, uses
    `getSideloadedVKsCarrier @prevsSpec unit`)
  - `2079` — `preComputeStepDomainLog2` (Effect-typed, same)
  - `2190` — `stepSolveAndProve` (m-polymorphic, runs StepProverT;
    needs `pure adv.sideloadedVKs`)
- `packages/pickles/src/Pickles/Prove/Compile.purs`
  - `1122` — `mkStepAdvice` for `PrevsSpecCons`
  - `1633` — `mkStepAdvice` for `PrevsSpecSideLoadedCons` (has
    `headVk` in scope)
- `packages/pickles/src/Pickles/Sideload/Advice.purs`
  - `144` — `MkUnitVkCarrier` class + instances
  - `122` — `SideloadedVKsM Effect carrier` instance
- `packages/pickles/test/Test/Pickles/Sideload/Loader.purs` — already
  works; consumes `sideload_main_child/` fixture.

## Once M6 is done, M7+ scaffolding

Test file at `packages/pickles/test/Test/Pickles/Prove/SideLoadedMain.purs`
(I wrote a draft and reverted; rewrite cleanly):

- Spec shape: `RulesCons 1 stmt (PrevsSpecSideLoadedCons 2 stmt
  PrevsSpecNil) (Tuple1 Unit) RulesNil`. Note **mpvMax=2** for the
  side-loaded slot (the side-loaded tag's compile-time bound), even
  though the actual child has mpv=N0.
- mkRuleEntry call: `mkRuleEntry @1 @Unit @(F StepField)
  simpleChainRule (tuple1 unit)` — `tuple1 unit` is the per-slot
  compile-time wrap key carrier (`Tuple1 Unit` for the side-loaded
  slot, since side-loaded slots have no compile-time wrap key).
- Reuse `simpleChainRule` from `Test.Pickles.Prove.SimpleChain` —
  rule body is identical.
- Load the side-loaded VK via `loadNrrFixture
  "packages/pickles/test/fixtures/sideload_main_child"`. Construct
  `Sideload.VerificationKey { circuit: <Checked from loaded data>,
  wrapVk: Just <hydrated VK> }`.
- Pass the constructed VK as the runtime side-loaded VK at prove
  time. With M6 done via the StepAdvice route, the test passes it
  via `compileMulti`'s vkCarrier input — exact mechanism depends on
  the M6 wiring.

## Acceptance criterion for M6 (re-spelled)

- The new test file (`SideLoadedMain.purs`) type-checks under `npx
  spago build -p pickles`.
- The test runs `compileMulti @SideLoadedMainRules` and gets back a
  `BranchProver` without crashing. (Prove-time invocation is M7,
  intentionally NOT in this milestone.)
- Existing pickles tests (NoRecursionReturn, SimpleChain,
  TwoPhaseChain, TreeProofReturn, ExpandDeferredEq, all 4 Sideload
  specs) still pass — no regression from the StepAdvice extension.

## Workflow / commands

- Build: `PATH="/home/martyall/.nvm/versions/node/v23.11.1/bin:$PATH"
  npx spago build -p pickles`
- Type-check fast (no JS codegen): `shopt -s globstar;
  PATH="..."npx purs compile -g corefn $(npx spago sources -p pickles
  2>/dev/null) --json-errors`
- Run all pickles tests: `npx spago test -p pickles`
- Run only side-loaded specs: `npx spago test -p pickles -- --example
  "Sideload"`

## Don't forget

- Node 23 required (`PATH="/home/martyall/.nvm/versions/node/v23.11.1/bin:$PATH"`).
- The pre-existing `packages/pickles/test/Test/Pickles/Sideload/`
  directory is untracked; existing files (Loader.purs,
  RoundTripNrrSpec.purs, etc.) are intentionally not yet committed.
  M5's commit added Loader.purs + RoundTripMainChildSpec.purs only.
  Don't accidentally `git add` the directory.
- The new SideloadedVKsM instance must NOT overlap with the existing
  Effect instance. The Effect instance is keyed on `m = Effect`; the
  new one on `m = StepProverT ...`. Different m's → no overlap.
