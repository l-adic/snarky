-- | **SCRATCH MODULE — Phase 2a skeleton for multi-branch compile.**
-- |
-- | This is a **stub** establishing the user-facing API surface for
-- | multi-branch (= N rules in one `Pickles.compile_promise` call
-- | sharing one wrap VK). Bodies are unimplemented; calling
-- | `compileMulti` raises `Exc.error`. Phase 2a's purpose is to commit
-- | the type signatures so we can iterate on shape before sinking
-- | implementation effort.
-- |
-- | Mirrors the existing `Pickles.Step.Prevs` pattern — that module
-- | encodes a per-prev-slot HList as a `PrevsSpec` kind plus
-- | `Tuple`-based value-level carriers; we encode the per-rule HList
-- | as a `RulesSpec` kind plus `Tuple`-based carriers in exactly the
-- | same shape, just one level up (rules list instead of prevs list).
-- | N-ary from the start; no `compileMulti2` placeholder.
-- |
-- | OCaml reference: `Pickles.compile_promise () ~choices:(fun ~self -> [...])`
-- | where the `[...]` list is what `RulesSpec` models at the type
-- | level and `rulesCarrier` (a Tuple chain) holds at the value level.
-- | Concrete fixture: `dump_two_phase_chain.exe` (2 rules; will scale
-- | naturally to transaction-snark-shape 5-rule cases later).
-- |
-- | What Phase 2a lands:
-- |
-- |   * `RulesSpec` kind + `RulesNil` / `RulesCons` constructors.
-- |   * Tuple-based value-level rule carriers.
-- |   * `CompileMultiConfig` and `MultiOutput` types holding per-rule
-- |     `slotVKs` carriers + per-rule prover carriers.
-- |   * `compileMulti` stub that throws `notImplemented`.
-- |
-- | What Phase 2b adds:
-- |
-- |   * `CompilableRulesSpec` class methods (analog of `CompilableSpec`
-- |     for the rules level): per-rule step compile + shared wrap
-- |     compile + per-rule prover wrapping.
-- |   * `MaxMpv` / `RulesLength` type families.
-- |   * `RulesCarrier` instance for `Tuple` chains.
module Pickles.Prove.CompileMulti
  ( -- * Type-level rules spec
    RulesSpec
  , RulesNil
  , RulesCons
  -- * Public API surface (Phase 2a stubs)
  , CompileMultiConfig
  , MultiOutput
  , MultiVKs
  , compileMulti
  -- * Structural carrier class (Phase 2b.20 split — light, no shape data)
  , class CompilableRulesSpec
  , branchCount
  , extractStepCompileFns
  , extractStepProveFns
  , runStepCompiles
  , buildWrapPerBranchVec
  -- * Shape-data class (Phase 2b.20 split — heavy, demands CompilableSpec)
  , class CompilableRulesSpecShape
  , runMultiCompile
  , runMultiCompileFull
  , buildBranchProvers
  -- * Per-rule context construction (Phase 2b.13)
  , buildStepProveCtx
  -- * End-to-end step + carrier conversion (Phase 2b.17)
  , compileMultiStepWrap
  -- * Smart-constructor probe (Phase 2b.4 — rules-side carrier shape)
  , RuleEntry(..)
  , mkRuleEntry
  -- * Misc
  , notImplemented
  ) where

import Prelude

import Control.Monad.Except (ExceptT)
import Control.Monad.Trans.Class (lift)
import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (error, throwException)
import Type.Proxy (Proxy(..))
import Pickles.Prove.Compile
  ( class CompilableSpec
  , ProveError
  , StepInputs
  , Tag
  , shapeCompileData
  )
import Pickles.ProofFFI (pallasProverIndexDomainLog2)
import Pickles.Prove.Step
  ( StepAdvice
  , StepCompileResult
  , StepProveContext
  , StepProveResult
  , StepRule
  , preComputeStepDomainLog2
  , stepCompile
  , stepSolveAndProve
  ) as PProveStep
import Pickles.Prove.Verify (CompiledProof, Verifier)
import Pickles.Prove.Wrap (WrapCompileResult, buildWrapMainConfigMulti, wrapCompile)
import Pickles.Step.Prevs (class PrevValuesCarrier, class PrevsCarrier)
import Pickles.Types (PaddedLength, StatementIO, StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Wrap.Slots (class PadSlots)
import Pickles.Dummy (wrapDomainLog2ForProofsVerified)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Types.Shifted (SplitField, Type2)

--------------------------------------------------------------------------------
-- Type-level rules spec
--
-- Mirrors `Pickles.Step.Prevs.PrevsSpec` (which encodes a per-prev-slot
-- HList) but at the rules level. Each `RulesCons` slot carries the
-- four type-level facts about that branch's rule:
--
--   1. `mpv`         — that branch's `max_proofs_verified`.
--   2. `valCarrier`  — heterogeneous tuple of prev statement types
--                      for THAT branch's prev slots.
--   3. `prevsSpec`   — that branch's prevs HList (in the existing
--                      `PrevsSpec` kind).
--   4. `slotVKs`     — that branch's per-slot imported-VK carrier.
--
-- All four vary per-branch. The shared types — `inputVal`, `outputVal`,
-- `prevInputVal` — live at the multi-branch level (they parameterize
-- the SHARED wrap VK's public-input layout), not in `RulesSpec`.
--------------------------------------------------------------------------------

-- | Kind: a type-level list of rule specs.
data RulesSpec

-- | Empty rules list. A multi-branch compile with `RulesNil` is
-- | structurally a no-op and should be rejected at the API level
-- | (Phase 2b enforces via instance unavailability).
foreign import data RulesNil :: RulesSpec

-- | One branch's contribution to the rules list. The four type-level
-- | parameters bind that branch's mpv / valCarrier / prevsSpec /
-- | slotVKs; the fifth is the rest of the list.
foreign import data RulesCons :: Int -> Type -> Type -> Type -> RulesSpec -> RulesSpec

--------------------------------------------------------------------------------
-- CompileMultiConfig
--
-- The user supplies:
--
--   * Shared SRS (one wrap VK across all branches).
--   * `debug` flag.
--   * `wrapDomainOverride` (analog of single-rule `Maybe Int`).
--   * `rulesCarrier` — value-level chain of per-rule data, shaped to
--     match `rs` via `Tuple … (Tuple … Unit)`. Each entry holds:
--       - the `StepRule` value for that branch
--       - that branch's `slotVKs` (per-prev-slot VK references)
--     For a 2-rule spec `RulesCons _ _ _ _ (RulesCons _ _ _ _ RulesNil)`
--     the carrier shape is `Tuple entry1 (Tuple entry2 Unit)`.
--     Phase 2b refines `entry`'s record shape to the precise per-rule
--     contents `compile` needs — for the skeleton it's opaque.
--------------------------------------------------------------------------------

-- | Multi-branch compile config. Shape is shared across all branches;
-- | per-branch data lives in the value-level `rulesCarrier` argument
-- | passed alongside.
type CompileMultiConfig =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , debug :: Boolean
  , wrapDomainOverride :: Maybe Int
  }

--------------------------------------------------------------------------------
-- MultiOutput
--
-- The "one VK, N provers" multi-branch invariant in the type:
--
--   * `proversCarrier` — Tuple chain matching `rs` shape, one entry
--     per branch holding that branch's `prover.step` closure.
--   * `tag` — single shared tag for the proof system. Its `mpv`
--     parameter is the max over all rules' mpvs (Phase 2b derives via
--     a `MaxMpv rs mpvMax` family).
--   * `verifier` — single shared verifier. ANY branch's proof
--     verifies under it.
--   * `vks` — bundles the shared wrap CompileResult + per-branch
--     step CompileResults (Tuple chain).
--   * `perBranchProverVKs` — Tuple chain of per-branch `ProverVKs`
--     handles for downstream `External` references.
--------------------------------------------------------------------------------

-- | Per-branch prover for ONE branch. Each `RulesCons` slot in the
-- | carrier corresponds to a `BranchProver` of that branch's shape.
-- | Aliases the type to make per-branch carriers readable.
type BranchProver
  :: Type -> Int -> Type -> Type -> Type -> (Type -> Type) -> Type
type BranchProver prevsSpec mpv prevsCarrier inputVal outputVal m =
  StepInputs prevsSpec inputVal prevsCarrier
  -> ExceptT ProveError m
       (CompiledProof mpv (StatementIO inputVal outputVal) outputVal Unit)

-- | Shared verification keys for a multi-branch compile.
-- |
-- | * `wrap` — the SINGLE wrap CompileResult. ANY branch's wrap proof
-- |   verifies under this VK; `whichBranch` in the wrap statement
-- |   distinguishes which step circuit produced the wrapped proof.
-- | * `perBranchStep` — Tuple chain of `StepCompileResult`s, one per
-- |   branch. These are NOT shared (each branch has its own step
-- |   circuit / step VK), but they're bundled here so callers have
-- |   one handle to all per-branch artifacts.
-- | * `wrapDomainLog2` — same value as in single-rule `ProverVKs`.
type MultiVKs perBranchStepCarrier =
  { wrap :: WrapCompileResult
  , perBranchStep :: perBranchStepCarrier
  , wrapDomainLog2 :: Int
  }

-- | Output of `compileMulti`. The multi-branch invariant in types:
-- | per-rule `provers` (one prover per branch via Tuple carrier) +
-- | ONE shared `tag` / `verifier` / `vks`.
type MultiOutput
  :: Type
  -> Type
  -> Int
  -> Type
  -> Type
  -> Type
  -> Type
type MultiOutput proversCarrier perBranchStepCarrier mpvMax inputVal outputVal perBranchVKsCarrier =
  { provers :: proversCarrier
  , tag :: Tag inputVal outputVal mpvMax
  , verifier :: Verifier
  , vks :: MultiVKs perBranchStepCarrier
  -- | Per-branch `ProverVKs` handles, in case the caller wants to
  -- | reference an individual branch from a different proof system
  -- | via `External` (e.g., blockchain_snark referencing a specific
  -- | branch of transaction_snark).
  , perBranchVKs :: perBranchVKsCarrier
  }

--------------------------------------------------------------------------------
-- CompilableRulesSpec — Phase 2b.9: structural recursion enabled
--
-- Mirror of `Pickles.Step.Prevs.PrevsCarrier` at the rules level
-- (one level up from per-prev-slot). Drives multi-branch compile
-- via per-rule dispatch.
--
-- Why class-method dispatch (vs. tuple-stored rules): PS rejects
-- record fields holding `StepRule`'s rank-2 forall (PR #126's wall +
-- Phase 2b.1's experiment confirmed). Class-method dispatch sidesteps
-- this — each instance is monomorphic, so the user's rank-2 rule
-- value gets *used* inside the method body (calling `stepCompile` /
-- `stepSolveAndProve`) without ever being *stored* as a record value.
--
-- The funDep `rs -> branches mpvMax` says: the type-level rules spec
-- determines (a) the branch count and (b) the max mpv across rules.
-- Phase 2b.9 wires the `Add restBranches 1 branches` recurrence so
-- branches is computed at the type level. mpvMax (max over rules)
-- is wired in a later phase — needs a Prim.Int.Compare-driven
-- type-level max relation.
--
-- The method `branchCount` validates the recursion is structurally
-- sound: for `RulesCons _ _ _ _ rest`, returns 1 + countBranches @rest;
-- for `RulesNil`, returns 0. Pure type-level recursion driving a
-- value-level integer.
--------------------------------------------------------------------------------

class CompilableRulesSpec
  :: RulesSpec
  -> Type
  -> Type
  -> Type
  -> Int
  -> Int
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
  -> Constraint
class
  CompilableRulesSpec rs inputVal outputVal prevInputVal branches mpvMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    selfStepDomainLog2sCarrier
    stepProveFnsCarrier
  | rs ->
      branches mpvMax rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
        perBranchStepCompileResults selfStepDomainLog2sCarrier
        stepProveFnsCarrier
  where
  -- | Count branches by structural recursion. Validates that
  -- | `branches` is correctly derived as a function of `rs` and that
  -- | the recurrence relation discharges (Cons case adds 1 to the
  -- | rest's count). Returns the same value `Reflectable branches`
  -- | would, but via direct class-method dispatch.
  branchCount :: forall proxy. proxy rs -> Int

  -- | Extract each `RuleEntry`'s `stepCompileFn` field into a Tuple
  -- | chain whose shape mirrors `rulesCarrier`. Pure value-level
  -- | rewriting: each per-rule entry yields its already-captured
  -- | `StepProveContext mpv -> Effect StepCompileResult` thunk.
  -- |
  -- | The output Tuple chain is heterogeneous — branch i's thunk has
  -- | type `StepProveContext mpv_i -> Effect StepCompileResult`, where
  -- | `mpv_i` is that branch's `max_proofs_verified`.
  extractStepCompileFns :: rulesCarrier -> stepCompileFnsCarrier

  -- | Run per-branch step compiles. Takes a Tuple chain of per-branch
  -- | `StepProveContext mpv` (caller-supplied; Phase 2b.12 leaves
  -- | their construction to the caller) and the rules carrier;
  -- | sequences each entry's `stepCompileFn ctx` and returns a Tuple
  -- | chain of `StepCompileResult`s in branch order.
  -- |
  -- | This is the per-branch step compile dispatch. The compile
  -- | thunks are accessed via `RuleEntry`'s field; the per-branch
  -- | context comes from the parallel input carrier.
  -- |
  -- | Phase 2b.13 will lift the context construction into the class
  -- | itself — given `CompileMultiConfig`, derive per-branch
  -- | `StepProveContext` via `shapeCompileData` (per-rule
  -- | `CompilableSpec` constraint added then).
  runStepCompiles
    :: perBranchCtxsCarrier
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | Symmetric to `extractStepCompileFns`: pull each entry's
  -- | `stepProveFn` into a Tuple chain. The per-branch thunk type:
  -- |
  -- |   StepProveContext mpv
  -- |   -> StepCompileResult
  -- |   -> StepAdvice prevsSpec _ _ inputVal mpv carrier valCarrier
  -- |   -> ExceptT EvaluationError Effect (StepProveResult outputSize)
  -- |
  -- | Used downstream (Phase 2b.20+) to build per-branch
  -- | `BranchProver` closures by composing stepSolveAndProve with the
  -- | wrap solve+prove flow.
  extractStepProveFns :: rulesCarrier -> stepProveFnsCarrier

  -- | Convert the per-branch `StepCompileResult` Tuple chain into the
  -- | `Vector branches { mpv, stepDomainLog2, stepVK }` shape that
  -- | `buildWrapMainConfigMulti` expects.
  -- |
  -- | For each branch:
  -- |   * `mpv` — reflected from the rule's type-level mpv (each Cons
  -- |     instance has `Reflectable ruleMpv Int`).
  -- |   * `stepDomainLog2` — extracted from the proverIndex via
  -- |     `pallasProverIndexDomainLog2`.
  -- |   * `stepVK` — the StepCompileResult's `verifierIndex` field.
  -- |
  -- | The Tuple → Vector accumulation is via `Vector.cons`. Each Cons
  -- | instance contributes one element; Nil contributes `Vector.nil`.
  buildWrapPerBranchVec
    :: perBranchStepCompileResults
    -> Vector branches
         { mpv :: Int
         , stepDomainLog2 :: Int
         , stepVK :: VerifierIndex VestaG StepField
         }

instance
  CompilableRulesSpec RulesNil inputVal outputVal prevInputVal 0 0 Unit Unit
    Unit
    Unit
    Unit
    Unit
  where
  branchCount _ = 0
  extractStepCompileFns _ = unit
  runStepCompiles _ _ = pure unit
  extractStepProveFns _ = unit
  buildWrapPerBranchVec _ = Vector.nil

-- | Cons instance: per-rule branch increments the running count via
-- | `Add restBranches 1 branches`. The Tuple carrier shape is pinned
-- | by `PrevsCarrier prevsSpec … carrier` (carrier from prevsSpec) and
-- | by Add chains (outputSize from mpv). These constraints feed back
-- | into the funDep `rs -> rulesCarrier` resolution.
instance
  ( CompilableRulesSpec rest inputVal outputVal prevInputVal
      restBranches restMpvMax restCarrier restStepCompileFns restCtxs
      restStepCompileResults restLog2s restStepProveFns
  , Add restBranches 1 branches
  , PrevsCarrier
      prevsSpec
      StepIPARounds
      WrapIPARounds
      (F StepField)
      (Type2 (SplitField (F StepField) Boolean))
      Boolean
      ruleMpv
      carrier
  , Mul ruleMpv 32 unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs ruleMpv outputSize
  , Reflectable ruleMpv Int
  -- TODO: Max ruleMpv restMpvMax mpvMax — needs a class encoding type-level max.
  ) =>
  CompilableRulesSpec
    (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
    inputVal outputVal prevInputVal
    branches
    mpvMax
    ( Tuple
        ( RuleEntry prevsSpec ruleMpv valCarrier inputVal carrier outputSize
            slotVKs
        )
        restCarrier
    )
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv -> Effect PProveStep.StepCompileResult
        )
        restStepCompileFns
    )
    (Tuple (PProveStep.StepProveContext ruleMpv) restCtxs)
    (Tuple PProveStep.StepCompileResult restStepCompileResults)
    (Tuple Int restLog2s)
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv
          -> PProveStep.StepCompileResult
          -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
               inputVal ruleMpv carrier valCarrier
          -> ExceptT EvaluationError Effect
               (PProveStep.StepProveResult outputSize)
        )
        restStepProveFns
    )
  where
  branchCount _ =
    1 + branchCount
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @restBranches
      @restMpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restLog2s
      @restStepProveFns
      (Proxy :: Proxy rest)
  extractStepCompileFns (Tuple (RuleEntry r) rest) =
    Tuple r.stepCompileFn
      ( extractStepCompileFns
          @rest
          @inputVal
          @outputVal
          @prevInputVal
          @restBranches
          @restMpvMax
          @restCarrier
          @restStepCompileFns
          @restCtxs
          @restStepCompileResults
          @restLog2s
          @restStepProveFns
          rest
      )
  runStepCompiles (Tuple ctx restCtxs) (Tuple (RuleEntry r) restEntries) = do
    headResult <- r.stepCompileFn ctx
    tailResults <- runStepCompiles
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @restBranches
      @restMpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restLog2s
      @restStepProveFns
      restCtxs
      restEntries
    pure (Tuple headResult tailResults)
  buildWrapPerBranchVec (Tuple headResult restResults) =
    let
      headRecord =
        { mpv: reflectType (Proxy :: Proxy ruleMpv)
        , stepDomainLog2: pallasProverIndexDomainLog2 headResult.proverIndex
        , stepVK: headResult.verifierIndex
        }
      restVec = buildWrapPerBranchVec
        @rest
        @inputVal
        @outputVal
        @prevInputVal
        @restBranches
        @restMpvMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restLog2s
        @restStepProveFns
        restResults
    in
      headRecord :< restVec
  extractStepProveFns (Tuple (RuleEntry r) rest) =
    Tuple r.stepProveFn
      ( extractStepProveFns
          @rest
          @inputVal
          @outputVal
          @prevInputVal
          @restBranches
          @restMpvMax
          @restCarrier
          @restStepCompileFns
          @restCtxs
          @restStepCompileResults
          @restLog2s
          @restStepProveFns
          rest
      )

--------------------------------------------------------------------------------
-- CompilableRulesSpecShape — Phase 2b.20 split: shape-data methods.
--
-- Why a separate class: the structural class above must NOT carry a
-- `CompilableSpec` super-constraint on its Cons instance, because PS
-- can't always discharge it at call sites (some sub-constraint on
-- PrevsSpecCons fails to dispatch from caller context, which cascades
-- through the funDep chain and leaves all class params unresolved).
-- Empirically verified: removing the constraint unblocks the
-- structural test probe.
--
-- This class extends `CompilableRulesSpec` with the shape-data
-- methods (runMultiCompile, runMultiCompileFull). The Cons instance
-- here DOES require `CompilableSpec prevsSpec ...`. Callers of these
-- methods opt in to the heavier discharge requirement; structural
-- methods stay light.
--
-- The split mirrors how single-rule `compile` separates structural
-- helpers (PrevsCarrier traversal) from shape-data computation
-- (CompilableSpec methods).
--------------------------------------------------------------------------------

class CompilableRulesSpec rs inputVal outputVal prevInputVal branches mpvMax
        rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
        perBranchStepCompileResults selfStepDomainLog2sCarrier
        stepProveFnsCarrier
   <= CompilableRulesSpecShape rs inputVal outputVal prevInputVal branches mpvMax
        rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
        perBranchStepCompileResults selfStepDomainLog2sCarrier
        stepProveFnsCarrier
        proversCarrier
  | rs -> branches mpvMax rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
        perBranchStepCompileResults selfStepDomainLog2sCarrier stepProveFnsCarrier
        proversCarrier
  where
  -- | High-level per-branch compile with caller-supplied per-rule
  -- | `selfStepDomainLog2`s. Walks the rules carrier and calls each
  -- | entry's `stepCompileFn` with a `StepProveContext` derived via
  -- | `buildStepProveCtx @prevsSpec`.
  runMultiCompile
    :: CompileMultiConfig
    -> selfStepDomainLog2sCarrier
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | End-to-end per-branch compile with the pre-pass internalized.
  -- | Per-rule flow: build placeholder ctx with log2=20, run pre-pass
  -- | to get real selfStepDomainLog2, build real ctx, call stepCompile.
  runMultiCompileFull
    :: CompileMultiConfig
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | Build per-branch `BranchProver` Tuple chain. Each closure runs
  -- | step solve+prove (via the rule's `stepProveFn`) and wrap
  -- | solve+prove with `whichBranch = branchIdx`.
  -- |
  -- | The leading `Int` is the BRANCH INDEX of the head entry. Top-
  -- | level callers pass `0`; the Cons body recurses with `idx + 1`
  -- | so each branch's closure can capture the right `whichBranch`
  -- | value for its wrap statement.
  -- |
  -- | Closure body is `notImplemented` until Phase 2b.24 (the
  -- | multi-branch runProverBody analog). The full implementation
  -- | needs `mkStepAdvice @prevsSpec` (in scope via the
  -- | `CompilableSpec` constraint), `shapeProveData @prevsSpec`,
  -- | `stepSolveAndProve` (via the rule's `stepProveFn`), and
  -- | `wrapSolveAndProve` with the captured branch index baked into
  -- | the wrap statement.
  buildBranchProvers
    :: Int
    -> CompileMultiConfig
    -> WrapCompileResult
    -> perBranchStepCompileResults
    -> selfStepDomainLog2sCarrier
    -> rulesCarrier
    -> Effect proversCarrier

instance
  CompilableRulesSpecShape RulesNil inputVal outputVal prevInputVal 0 0
    Unit Unit Unit Unit Unit Unit Unit
  where
  runMultiCompile _ _ _ = pure unit
  runMultiCompileFull _ _ = pure unit
  buildBranchProvers _ _ _ _ _ _ = pure unit

instance
  ( CompilableRulesSpecShape rest inputVal outputVal prevInputVal
      restBranches restMpvMax restCarrier restStepCompileFns restCtxs
      restStepCompileResults restLog2s restStepProveFns restProvers
  , CompilableSpec prevsSpec slotVKs prevsCarrier ruleMpv slots valCarrier
      carrier
  , CompilableRulesSpec
      (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
      inputVal outputVal prevInputVal branches mpvMax
      ( Tuple
          ( RuleEntry prevsSpec ruleMpv valCarrier inputVal carrier outputSize
              slotVKs
          )
          restCarrier
      )
      ( Tuple
          ( PProveStep.StepProveContext ruleMpv -> Effect PProveStep.StepCompileResult
          )
          restStepCompileFns
      )
      (Tuple (PProveStep.StepProveContext ruleMpv) restCtxs)
      (Tuple PProveStep.StepCompileResult restStepCompileResults)
      (Tuple Int restLog2s)
      ( Tuple
          ( PProveStep.StepProveContext ruleMpv
            -> PProveStep.StepCompileResult
            -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
                 inputVal ruleMpv carrier valCarrier
            -> ExceptT EvaluationError Effect
                 (PProveStep.StepProveResult outputSize)
          )
          restStepProveFns
      )
  ) =>
  CompilableRulesSpecShape
    (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
    inputVal outputVal prevInputVal
    branches mpvMax
    ( Tuple
        ( RuleEntry prevsSpec ruleMpv valCarrier inputVal carrier outputSize
            slotVKs
        )
        restCarrier
    )
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv -> Effect PProveStep.StepCompileResult
        )
        restStepCompileFns
    )
    (Tuple (PProveStep.StepProveContext ruleMpv) restCtxs)
    (Tuple PProveStep.StepCompileResult restStepCompileResults)
    (Tuple Int restLog2s)
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv
          -> PProveStep.StepCompileResult
          -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
               inputVal ruleMpv carrier valCarrier
          -> ExceptT EvaluationError Effect
               (PProveStep.StepProveResult outputSize)
        )
        restStepProveFns
    )
    ( Tuple
        ( BranchProver prevsSpec ruleMpv prevsCarrier inputVal outputVal Effect
        )
        restProvers
    )
  where
  runMultiCompile cfg (Tuple log2 restLog2s) (Tuple (RuleEntry r) restEntries) = do
    let
      ctx = buildStepProveCtx @prevsSpec cfg r.slotVKs log2
    headResult <- r.stepCompileFn ctx
    tailResults <- runMultiCompile
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @restMpvMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      cfg
      restLog2s
      restEntries
    pure (Tuple headResult tailResults)
  runMultiCompileFull cfg (Tuple (RuleEntry r) restEntries) = do
    let
      placeholderCtx = buildStepProveCtx @prevsSpec cfg r.slotVKs 20
    selfStepDomainLog2 <- r.preComputeStepDomainLog2Fn placeholderCtx
    let
      realCtx = buildStepProveCtx @prevsSpec cfg r.slotVKs selfStepDomainLog2
    headResult <- r.stepCompileFn realCtx
    tailResults <- runMultiCompileFull
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @restMpvMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      cfg
      restEntries
    pure (Tuple headResult tailResults)
  buildBranchProvers branchIdx cfg wrapResult
    (Tuple _headStepCR restStepResults)
    (Tuple _headLog2 restLog2s)
    (Tuple (RuleEntry _r) restEntries) = do
    -- Phase 2b.23: branchIdx threaded through. Per-branch closure
    -- captures it for wrap-statement `whichBranch` (Phase 2b.24).
    let
      thisBranch = branchIdx
      headProver = \_stepInputs ->
        lift $ notImplemented
          ("buildBranchProvers head closure (branch " <> show thisBranch <> ")")
    restProvers <- buildBranchProvers
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @restMpvMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      (branchIdx + 1)
      cfg
      wrapResult
      restStepResults
      restLog2s
      restEntries
    pure (Tuple headProver restProvers)

--------------------------------------------------------------------------------
-- RuleEntry / mkRuleEntry — Phase 2b.4 probe of the rules-side
-- carrier shape.
--
-- Phase 2b.1 found: storing `StepRule mpv …` (a rank-2 forall over
-- `t` and `m'`) in a record field rejected by PS — the same wall PR
-- #126 hit.
--
-- Probe hypothesis: capture the rank-2 rule INSIDE a closure whose
-- outer type is monomorphic. `RuleEntry` holds Effect-typed action
-- closures (compile / prove) that internally use the rule's rank-2
-- nature when invoked, but the stored field types are non-rank-2.
-- PS rejects rank-2 *storage* but should be fine with rank-2 *use
-- inside a closure body*.
--
-- If this probe compiles, we have the path forward for `compileMulti`'s
-- input shape: a Tuple chain of `RuleEntry`s. If it doesn't, the
-- rank-2 wall is even higher than thought and we need a typeclass-
-- based dispatch instead.
--
-- For Phase 2b.4 the bodies are stubbed (`notImplemented`) — we're
-- testing only that the SIGNATURES type-check.
--------------------------------------------------------------------------------

-- | Per-rule entry packaged for storage in a multi-branch carrier.
-- |
-- | Stored fields are intentionally NOT the rank-2 `StepRule` —
-- | instead, monomorphic closures that capture the rule when
-- | constructed via `mkRuleEntry`. PS handles the rank-2 nature at
-- | the closure body's call site (where the rule is applied to
-- | specific `t` / `m'`), not at the record-field level.
-- |
-- | Phase 2b.6: `stepCompileFn` body delegates to `stepCompile` with
-- | the captured rule.
-- | Phase 2b.7: `stepProveFn` body delegates to `stepSolveAndProve`
-- | with the captured rule. Both rank-2-use paths typecheck — the
-- | smart-constructor pattern is end-to-end viable.
-- |
-- | The kind expansion vs Phase 2b.6 — adding `prevsSpec`, `inputVal`,
-- | `carrier`, `outputSize` — is needed because `stepProveFn`'s field
-- | type references those (in `StepAdvice` and `StepProveResult`).
-- | They were already pinned by `mkRuleEntry`'s outer signature in
-- | Phase 2b.6 via class constraints; now they show in the result
-- | type because the prove closure's signature mentions them.
-- |
-- | Future: if exposing 7 type params on `RuleEntry` is unergonomic
-- | for downstream Tuple carriers, we can pack them into a single
-- | existential newtype around `RuleEntry`. Phase 2b.8 decision.
data RuleEntry
  :: Type
  -> Int
  -> Type
  -> Type
  -> Type
  -> Int
  -> Type
  -> Type
data RuleEntry prevsSpec mpv valCarrier inputVal carrier outputSize slotVKs = RuleEntry
  { -- | Pre-pass: takes a placeholder `StepProveContext mpv` (built
    -- | with OCaml `rough_domains` log2=20) and returns the actual
    -- | `selfStepDomainLog2` derived by counting gates in a one-shot
    -- | constraint-system build. Phase 2b.15 — analog of OCaml's
    -- | `Fix_domains.domains` per-rule.
    preComputeStepDomainLog2Fn ::
      PProveStep.StepProveContext mpv -> Effect Int
  , stepCompileFn ::
      PProveStep.StepProveContext mpv -> Effect PProveStep.StepCompileResult
  , stepProveFn ::
      PProveStep.StepProveContext mpv
      -> PProveStep.StepCompileResult
      -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
           inputVal mpv carrier valCarrier
      -> ExceptT EvaluationError Effect (PProveStep.StepProveResult outputSize)
  , slotVKs :: slotVKs
  }

-- | Smart constructor: takes the user's rank-2 `StepRule` value and
-- | produces a `RuleEntry` with closures capturing it.
-- |
-- | Phase 2b.6 body: `stepCompileFn` calls `stepCompile` with the
-- | captured rule (the actual rank-2-use test). All visible-type
-- | applications and constraints needed by `stepCompile` are
-- | propagated through this signature, mirroring single-rule
-- | `runCompile` (`Pickles.Prove.Compile`). If this typechecks, the
-- | smart-constructor pattern is end-to-end viable for `compileMulti`.
mkRuleEntry
  :: forall @prevsSpec @mpv @outputSize @valCarrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar @slotVKs
       carrier carrierVar pad unfsTotal digestPlusUnfs
   . CircuitGateConstructor StepField VestaG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => PrevValuesCarrier prevsSpec valCarrier
  => PStepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> slotVKs
  -> Effect (RuleEntry prevsSpec mpv valCarrier inputVal carrier outputSize slotVKs)
mkRuleEntry rule slotVKs = pure $ RuleEntry
  { preComputeStepDomainLog2Fn: \ctx ->
      PProveStep.preComputeStepDomainLog2
        @prevsSpec
        @outputSize
        @valCarrier
        @inputVal
        @inputVar
        @outputVal
        @outputVar
        @prevInputVal
        @prevInputVar
        ctx
        rule
  , stepCompileFn: \ctx ->
      PProveStep.stepCompile
        @prevsSpec
        @outputSize
        @valCarrier
        @inputVal
        @inputVar
        @outputVal
        @outputVar
        @prevInputVal
        @prevInputVar
        ctx
        rule
  , stepProveFn: \ctx compileResult advice ->
      PProveStep.stepSolveAndProve
        @prevsSpec
        @outputSize
        @valCarrier
        @inputVal
        @inputVar
        @outputVal
        @outputVar
        @prevInputVal
        @prevInputVar
        ctx
        rule
        compileResult
        advice
  , slotVKs
  }

-- Local alias to avoid naming collision in imports if `StepRule`
-- appears elsewhere; the existing rank-2 type alias from
-- `Pickles.Prove.Step`. Defined as a type synonym to avoid an
-- import-cycle headache during this exploratory probe.
type PStepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar =
  PProveStep.StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar

--------------------------------------------------------------------------------
-- compileMulti — Phase 2a stub
--------------------------------------------------------------------------------

-- | Compile an N-branch multi-rule proof system.
-- |
-- | Phase 2a body: throws `notImplemented`. The signature establishes
-- | the API shape; Phase 2b fills the body.
-- |
-- | Type-variable layout (mirrors single-rule `compile`'s shape):
-- |
-- |   * `rs` (kind `RulesSpec`) — per-rule HList of `(mpv, valCarrier,
-- |     prevsSpec, slotVKs)` quadruples. The user picks `rs` shape
-- |     when invoking; Phase 2b derives carrier shapes from it via
-- |     class machinery.
-- |   * `rulesCarrier`, `proversCarrier`, `perBranchStepCarrier`,
-- |     `perBranchVKsCarrier` — Tuple chains shaped to match `rs`,
-- |     each holding per-rule data of a different sort. Phase 2b
-- |     adds `RulesCarrier` class instances for `RulesNil` /
-- |     `RulesCons` that derive these shapes mechanically.
-- |   * `inputVal` / `outputVal` / `prevInputVal` — SHARED across
-- |     all branches (the wrap VK's public-input layout is the same
-- |     for any proof under it).
-- |   * `mpvMax` — max over all rules' mpvs. Phase 2b derives via a
-- |     `MaxMpv rs mpvMax` type family.
-- |
-- | Implementation roadmap (Phase 2b):
-- |
-- |   1. Walk `rs`: per-rule, run `stepCompile` independently. Each
-- |      branch's step circuit is sized by ITS OWN prevsSpec /
-- |      max_proofs_verified.
-- |   2. ONE wrap compile with `branches = N` (drop the hardcoded
-- |      `wrapCompile @1` and thread per-branch `Vector branches Int`
-- |      arrays into `WrapMainConfig.{stepWidths, domainLog2s,
-- |      stepKeys}`).
-- |   3. Per-branch prover wraps `runProverBody` with that branch's
-- |      `whichBranch` field baked into the wrap statement.
-- | Phase 2a forall is trimmed to only the type vars that actually
-- | appear in the signature's input/output (PureScript rejects
-- | "unused type vars"). Phase 2b reintroduces:
-- |
-- |   * `rs :: RulesSpec` — driver for the carrier shapes via
-- |     `RulesCarrier` class instances.
-- |   * `prevInputVal` — shared prev statement type, threaded through
-- |     once carriers expose per-branch prevs.
-- |   * `m` — the prover monad, threaded through `BranchProver`.
-- |
-- | They'll all be visible-type-applicable at the call site (matching
-- | single-rule `compile`'s `@inputVal @outputVal @prevInputVal @m`
-- | pattern).
--------------------------------------------------------------------------------
-- buildStepProveCtx — derive a per-rule StepProveContext from
-- CompileMultiConfig + slotVKs + selfStepDomainLog2.
--
-- Wraps the existing single-rule `shapeCompileData @prevsSpec` in a
-- multi-branch-friendly interface: instead of taking a single-rule
-- `CompileConfig prevsSpec slotVKs`, take a `CompileMultiConfig`
-- (shared) plus the per-rule `slotVKs` (from the entry).
--
-- Phase 2b.14 will lift this call into a `CompilableRulesSpec` class
-- method that walks the rules carrier and threads per-branch contexts
-- into `runStepCompiles`.
--
-- Pre-pass (preComputeStepDomainLog2) is the caller's responsibility
-- for now — the pre-pass requires the rule's rank-2 forall, so it's
-- naturally another `RuleEntry` closure (Phase 2b.15). For initial
-- bring-up, callers can pass the OCaml `rough_domains` placeholder
-- value `20` and accept that the resulting circuit will use the
-- placeholder (overshoots real size; corrected by the pre-pass once
-- it lands).
--------------------------------------------------------------------------------

-- | Build a per-rule `StepProveContext` from the multi-branch config,
-- | the rule's `slotVKs`, and its `selfStepDomainLog2`. Used inside
-- | `CompilableRulesSpec`'s recursion to feed `runStepCompiles`.
-- |
-- | The per-rule `CompileConfig` is constructed by combining the
-- | shared `srs` / `debug` / `wrapDomainOverride` from the multi
-- | config with the rule's own `slotVKs`. `shapeCompileData
-- | @prevsSpec` then handles the per-prev-spec layout (per-slot
-- | lagrange basis, blinding H, FOP domains).
buildStepProveCtx
  :: forall @prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => CompileMultiConfig
  -> slotVKs
  -> Int
  -> PProveStep.StepProveContext mpv
buildStepProveCtx cfg slotVKs selfStepDomainLog2 =
  let
    perRuleCfg =
      { srs: cfg.srs
      , perSlotImportedVKs: slotVKs
      , debug: cfg.debug
      , wrapDomainOverride: cfg.wrapDomainOverride
      }
    shape = shapeCompileData @prevsSpec perRuleCfg selfStepDomainLog2
  in
    shape.stepProveCtx

--------------------------------------------------------------------------------
-- compileMultiStepWrap — Phase 2b.17 step + wrap end-to-end helper
--
-- Combines the per-branch step compile (`runMultiCompileFull`),
-- carrier conversion (`buildWrapPerBranchVec`), wrap config
-- construction (`buildWrapMainConfigMulti`), and wrap compile
-- (`wrapCompile`) into one shot.
--
-- Output: the per-branch step CompileResult Tuple chain + the
-- single shared WrapCompileResult.
--
-- Phase 2b.18 will wrap this in the full `compileMulti` API
-- (provers / tag / verifier / perBranchVKs).
--
-- The `lagrangeDomainLog2` is currently the wrap circuit's own
-- domain log2 (= `wrapDomainLog2`). The
-- `buildWrapMainConfigMulti` doc TODO flags this for witness-diff
-- validation against `dump_two_phase_chain.exe`. Single-rule
-- worked because step ≡ wrap when no override; multi-rule may
-- need a different choice — to be confirmed.
--------------------------------------------------------------------------------

compileMultiStepWrap
  :: forall @rs @inputVal @outputVal @prevInputVal @mpvMax @slots
       branches
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       selfStepDomainLog2sCarrier
       stepProveFnsCarrier
       proversCarrier
       branchesPred totalBases totalBasesPred
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal branches mpvMax
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       selfStepDomainLog2sCarrier
       stepProveFnsCarrier
       proversCarrier
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpvMax Int
  => Add 1 branchesPred branches
  => Compare mpvMax 3 LT
  => Add mpvMax 45 totalBases
  => Add 1 totalBasesPred totalBases
  => PadSlots slots mpvMax
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CompileMultiConfig
  -> rulesCarrier
  -> Effect
       { stepResults :: perBranchStepCompileResults
       , wrapResult :: WrapCompileResult
       , perBranchVec ::
           Vector branches
             { mpv :: Int
             , stepDomainLog2 :: Int
             , stepVK :: VerifierIndex VestaG StepField
             }
       }
compileMultiStepWrap cfg rules = do
  stepResults <- runMultiCompileFull
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    cfg
    rules
  let
    perBranchVec = buildWrapPerBranchVec
      @rs
      @inputVal
      @outputVal
      @prevInputVal
      stepResults
    -- Lagrange-domain log2: provisionally the wrap circuit's own
    -- domain log2 (= wrap_domains[mpvMax]). The
    -- buildWrapMainConfigMulti TODO flags this for witness-diff
    -- validation against dump_two_phase_chain.exe.
    lagrangeDomainLog2 =
      wrapDomainLog2ForProofsVerified (reflectType (Proxy :: Proxy mpvMax))
  wrapResult <- wrapCompile @branches @slots
    { wrapMainConfig:
        buildWrapMainConfigMulti @branches cfg.srs.vestaSrs
          { lagrangeDomainLog2, perBranch: perBranchVec }
    , crs: cfg.srs.pallasSrs
    }
  pure { stepResults, wrapResult, perBranchVec }

compileMulti
  :: forall @inputVal @outputVal @mpvMax
       rulesCarrier proversCarrier perBranchStepCarrier perBranchVKsCarrier
   . CompileMultiConfig
  -> rulesCarrier
  -> Effect
       ( MultiOutput
           proversCarrier
           perBranchStepCarrier
           mpvMax
           inputVal
           outputVal
           perBranchVKsCarrier
       )
compileMulti _cfg _rules = notImplemented "compileMulti"

-- | Standard not-implemented marker — throws an `Effect` exception so
-- | Phase 2a tests can `try` / `catchException` and surface a clean
-- | "skeleton not yet implemented" message rather than crashing the
-- | runtime opaquely.
notImplemented :: forall a. String -> Effect a
notImplemented label =
  throwException $ error $
    "Pickles.Prove.CompileMulti." <> label
      <> ": Phase 2a skeleton — not yet implemented. "
      <> "See module docstring + dump_two_phase_chain.ml for "
      <> "the multi-branch semantics being approximated."
