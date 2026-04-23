# Pickles `compile` → `Prover` API — implementation plan

Plan for replacing the hand-rolled `B0Producer` / `B1Producer` style test
scaffolding with a `Pickles.Prove.Compile.compile` function that returns
a `Prover` (with `step`) and a `Verifier` in one call, mirroring OCaml
`Pickles.compile_promise`.

## Background

Current state (after the verifier landing, PR #125):

- `Pickles.Prove.Verify` — user-facing verifier (done). `mkVerifier`,
  `verifyOne`, `verify`, `CompiledProof`, `Verifier`, `wrapPublicInput`.
- `Pickles.Prove.Pure.Verify` — `expandDeferredForVerify` port of OCaml
  `Wrap_deferred_values.expand_deferred`. Byte-identity-checked against
  `wrapComputeDeferredValues` on N=0 and N=1 cases.
- Five end-to-end tests pass in `VerifySmoke`: NRR b0, Simple_chain
  b0, Simple_chain b1 (inductive), Tree_proof_return b0, and the
  5-iteration SimpleChain chain.

Missing: a high-level `compile → Prover` API that replaces the ~300 lines
per-iteration producer code with a single call. That's what this plan
builds.

## Design recap

### Module layout

```
Pickles.Prove.Compile         NEW — user-facing compile + Prover
Pickles.Prove.Verify          existing — user-facing verifier
Pickles.Prove.Pure.Verify     existing — pure expand_deferred port

Pickles.Prove.Step            existing — low-level step prover (Compile wraps this)
Pickles.Prove.Wrap            existing — low-level wrap prover (Compile wraps this)
Pickles.Prove.Pure.{Step,Wrap} existing — pure helpers
```

### User-facing API shape

```purescript
compile
  :: forall prevsSpec mpv inputVal inputVar outputVal outputVar
       auxVal auxVar slotVKs m.
     Monad m
  => PrevsSpecLen prevsSpec mpv
  => PrevsInputsCarrier prevsSpec ...
  => PerSlotVKsCarrier prevsSpec slotVKs
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField auxVal auxVar
  => CompileConfig prevsSpec ... m
  -> { prover   :: Prover prevsSpec inputVal outputVal outputVar auxVal m
     , verifier :: Verifier
     , vks      :: ProverVKs
     }

type Prover prevsSpec inputVal outputVal outputVar auxVal m =
  { step :: StepInputs prevsSpec inputVal
         -> ExceptT ProveError m (CompiledProof mpv stmtVal outputVal auxVal)
  }

type StepInputs prevsSpec inputVal =
  { appInput :: inputVal
  , prevs    :: PrevsInputsCarrierOf prevsSpec  -- nested Tuple, heterogeneous
  }

type ProverVKs =  -- what downstream compiles consume as `perSlotImportedVKs`
  { stepVK :: VerifierIndex VestaG StepField
  , wrapVK :: VerifierIndex PallasG WrapField
  , wrapDomainLog2 :: Int
  }
```

The advice monad `m` is polymorphic so applications that need effects
during witness computation (logging, DB lookups in `exists` bodies,
etc.) can thread their own monad. Default is `Identity` / `Effect`
depending on FFI needs at the SRS layer.

### Key design decisions (already settled in conversation)

- **No Tags.** Prover records cross-reference each other as values via
  `perSlotImportedVKs`. OCaml's `Tag.t` lazy-init trick is unnecessary —
  PS types handle it directly at the type level.
- **No `PublicInputMode` class.** The rule signature
  `inputVar -> CircuitM outputVar` already encodes it — `Unit` on either
  side collapses via `CircuitType`.
- **No `auxiliaryTyp` parameter.** `CircuitType` constraint pins everything.
- **Pure API (except SRS).** SRS construction stays in user code; everything
  after `compile` is pure + `Monad m` polymorphic.
- **Verifier already done.** `mkVerifier` + `CompiledProof` are reused as-is.

### `StatementIO` — uniform statement shape

Every Pickles rule's statement (= what the verifier commits to as the
kimchi public input) has at most two components: the rule's main-function
**input** and its **returned output**. Existing Pickles tests use three
modes (`Input typ`, `Output typ`, `Input_and_output`), but all three are
captured uniformly by:

```purescript
newtype StatementIO input output = StatementIO
  { input :: input
  , output :: output
  }

derive instance Generic (StatementIO input output) _
derive instance Newtype (StatementIO input output) _

-- CircuitType derives automatically from the generic instance:
instance
  ( CircuitType f inputVal inputVar
  , CircuitType f outputVal outputVar
  ) =>
  CircuitType f
    (StatementIO inputVal outputVal)
    (StatementIO inputVar outputVar)
  where
    -- genericValueToFields / genericVarToFields etc.
```

Mode correspondence:

| OCaml mode | `StatementIO` form |
|---|---|
| `Input typ` | `StatementIO input Unit` |
| `Output typ` | `StatementIO Unit output` |
| `Input_and_output (i, o)` | `StatementIO input output` |

`CircuitType Unit Unit` has `sizeInFields = 0`, so the "unused" side
contributes no field elements to the kimchi public-input array — the
serialization matches OCaml's current byte layout for all three modes.

This gives us:
- **No `PublicInputMode` class needed** — mode is encoded in which side
  is `Unit`.
- **Uniform axis for `stmtVal`** in every API type — every prev's statement
  has the same shape, parameterized by `(input, output)`.
- **CircuitType for free** via generic derivation.

### Type-class machinery to add

1. `PrevsSpecLen prevsSpec mpv | prevsSpec -> mpv` — derive `mpv` from spec.
2. `PrevsInputsCarrier prevsSpec carrier | prevsSpec -> carrier` —
   user-facing heterogeneous input shape (nested Tuple of
   `PrevInputEntry n stmtVal stmtVar`). `stmtVar` is DERIVED via
   `CircuitType StepField stmtVal stmtVar` instead of being a direct
   parameter on `PrevsSpecCons`, since `CircuitType`'s fundep
   `a f -> var` uniquely determines it from `stmtVal + StepField`.
3. `PerSlotVKsCarrier prevsSpec carrier | prevsSpec -> carrier` — per-slot
   `Nothing` (self) or `Just otherProver.vks` (imported).

## Phased breakdown

Each phase lands as an independent commit with a clear green-signal test
and a concrete cleanup (deletions of now-redundant code).

### Phase 0 — introduce `StatementIO` + extend `PrevsSpec` with per-slot stmt

**Scope.**

1. Add `StatementIO input output` newtype with generic-derived `CircuitType`
   (module: `Pickles.Prove.Compile.Types` or `Pickles.Types`).
2. Extend `PrevsSpecCons` in `Pickles.Step.Prevs`:

```purescript
-- Before:
data PrevsSpecCons (n :: Int) rest

-- After (single-axis extension):
data PrevsSpecCons (n :: Int) statement rest
```

Ripple through every call site (stepCompile, stepSolveAndProve,
StepAdvice, the three B0/B1 producers, existing SimpleChain /
TreeProofReturn specs). At every existing site, uniformly instantiate
`statement = StatementIO <currentPrevInputVal> <currentPrevOutputVal>`.
For rules in Input mode, that's `StatementIO (F StepField) Unit`; for
Output mode, `StatementIO Unit (F StepField)`. No runtime change —
`StatementIO Unit X` / `StatementIO X Unit` / `StatementIO X Y` all
serialize to the same fields the kimchi verifier currently sees for
the corresponding mode.

The `stmtVar` axis is NOT added as a direct spec parameter — instance
heads that need it derive it via `CircuitType StepField statement
stmtVar` where needed.

**Test signal.** All existing tests still pass. The 5 verify tests + full
`spago test -p pickles`.

**Cleanup.** None (prep-only). Sets up the types all subsequent phases
consume.

**Alternatives considered.**

- *Parallel `CompilePrevsSpec*` types with a translation layer* —
  rejected: adds a permanent translation layer for what can be a
  one-time mechanical extension.
- *Two-axis extension (`stmtVal` + `stmtVar` both direct spec params)* —
  rejected: `CircuitType`'s fundep derives `stmtVar` from `stmtVal + f`
  uniquely, so carrying both is redundant. The single-axis version
  shrinks every existing call site's edit from two added type arguments
  to one.
- *Raw `stmtVal` type directly (no `StatementIO` wrapper)* — rejected:
  forces case-analysis-on-mode at every call site that wants to know
  whether the stmt is an input, an output, or both. `StatementIO` makes
  the shape uniform and the mode classification implicit.

### Phase 1 — `Pickles.Prove.Compile` for `PrevsSpecNil`

**Scope.**

- New module `Pickles.Prove.Compile` with `compile`, `Prover`,
  `StepInputs`, `ProverVKs`, `ProveError`, `CompileConfig`
- Three fundep classes with `PrevsSpecNil`-only instances:
  - `PrevsSpecLen PrevsSpecNil 0`
  - `PrevsInputsCarrier PrevsSpecNil Unit`
  - `PerSlotVKsCarrier PrevsSpecNil Unit`
- `compile` body: internally `stepCompile` → `wrapCompile` → returns a
  `Prover` whose `step` calls `buildStepAdvice` + `stepSolveAndProve` +
  the existing NRR wrap-prove flow
- `Prover` polymorphic in the advice monad `m`

**Test signal.** New test `Test.Pickles.Prove.CompileSmoke` (parallel to
`VerifySmoke`, same shape). Asserts:

1. `prover.step { appInput: unit, prevs: unit }` returns a `CompiledProof`
2. `verifier.verify [proof]` returns `true`
3. Resulting wrap proof byte-matches `produceNoRecursionReturn`
   (kimchi RNG is deterministic, seed 42)

**Cleanup.** Migrate the `"NRR b0 end-to-end"` case in `VerifySmoke` to
use `compile`. Delete `Test.Pickles.Prove.NoRecursionReturn.Producer`.
Reroute `Test.Pickles.Verify.ExpandDeferredEq`'s NRR case to use
`compile`'s internals (or expose a `wrapDvInput` artifact from the
Prover for convergence testing).

### Phase 2 — `PrevsSpecCons n (StatementIO i o) PrevsSpecNil` (single-slot)

**Scope.**

- Add `PrevsSpecCons`-with-`Nil`-tail instances to the three carrier
  classes
- Extend `compile` to handle a single slot — constructs `PrevInputEntry`
  carriers, builds step advice with oracles over the single prev, plumbs
  through step+wrap prove

**Test signal.** Migrate `"Simple_chain b0"` + `"Simple_chain b1"` cases
in `VerifySmoke` to `compile`. Both return `true`; wrap proofs byte-match
`produceSimpleChainB0` / `produceSimpleChainB1`.

**Cleanup.** Delete `Test.Pickles.Prove.SimpleChain.B0Producer` and
`B1Producer`. Simple_chain case in `ExpandDeferredEq` migrates similarly.

### Phase 3 — arbitrary `PrevsSpecCons` chains (heterogeneous multi-slot)

**Scope.**

- Recursive carrier instance:
  ```purescript
  instance
    ( CircuitType StepField stmt stmtVar
    , PrevsInputsCarrier rest restC
    ) =>
    PrevsInputsCarrier (PrevsSpecCons n stmt rest)
      (Tuple (PrevInputEntry n stmt stmtVar) restC)
  ```
  (+ parallel for `PerSlotVKsCarrier`). `stmt` is a `StatementIO i o`;
  `stmtVar` is derived from it via the `CircuitType` fundep.
- `compile` body iterates the carrier, builds per-slot advice
  heterogeneously
- `perSlotImportedVKs` accepts `Just otherProver.vks :< Nothing :< Nil`
- Handles `Tree_proof_return`'s N=2 shape

**Test signal.** Migrate `"Tree_proof_return b0"` case in `VerifySmoke`.
Key new assertion:
```purescript
compile treeConfig
  { perSlotImportedVKs = Just nrrProver.vks :< Nothing :< Nil, ... }
```
produces a prover whose step proofs verify.

**Cleanup.** Delete `Test.Pickles.Prove.TreeProofReturn.B0Producer`.

### Phase 4 — deferred coverage made trivial (closes task #131)

**Scope.** No API changes. Just test additions using the existing `compile`
infrastructure.

**Test signal.**

- `Tree_proof_return b1` (N=2 inductive) — one-liner:
  ```purescript
  treeProver.step
    { appInput
    , prevs: Tuple nrrPrev (Tuple treeB0Prev Nil)
    }
  ```
- Adversarial rejection — `verifier.verify` on a proof with a tampered
  statement returns `false`

**Cleanup.** Close task #131.

## Post-migration state

After Phase 3:

Gone:
- `NoRecursionReturn/Producer.purs`
- `SimpleChain/B0Producer.purs`
- `SimpleChain/B1Producer.purs`
- `TreeProofReturn/B0Producer.purs`

Shrunken:
- `VerifySmoke.purs` from ~210 lines → ~60 (each test becomes ~10 lines:
  `compile` + `prover.step` + assertion)

New line-count cost:
- `Pickles.Prove.Compile.purs` ≈ 250-400 lines (compile body + types)
- `PrevsInputsCarrier` / `PerSlotVKsCarrier` / `PrevsSpecLen` instance
  chain ≈ 80 lines

Net reduction: ~800 lines of hand-rolled producer code replaced by ~450
lines of generic API.

## Open questions deferred

- **Multi-branch tags.** OCaml `compile_promise` takes a list of rules
  per tag (`choices : self -> H4_6_with_length...`). Every PS test is
  single-branch. Add later if needed — not load-bearing for current use
  cases.
- **True amortized `batch_verify`.** Current `verify` folds single-proof
  kimchi verification; true batch is an additional Rust FFI function
  wrapping `kimchi::verifier::batch_verify` with multiple `Context`s.
  ~30 lines of Rust. Add the first time a caller needs batch throughput.

