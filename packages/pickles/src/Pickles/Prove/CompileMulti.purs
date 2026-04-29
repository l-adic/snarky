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
  , BranchProver(..)
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
  -- * Multi-branch prover body skeleton (Phase 2b.24a)
  , runMultiProverBody
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
import Data.Maybe (Maybe, fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (error, throwException)
import Type.Proxy (Proxy(..))
import Pickles.Prove.Compile
  ( class CompilableSpec
  , class PadProveDataMpv
  , PadProveDataDummies
  , padShapeProveData
  , ProveError
  , ShapeProveData
  , ShapeProveSideInfo
  , StepInputs
  , Tag
  , mkStepAdvice
  , shapeCompileData
  , shapeProveData
  )
import Effect.Class (liftEffect)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI
  ( pallasProofOpeningSg
  , pallasProofOracles
  , pallasProverIndexDomainLog2
  , permutationVanishingPolynomial
  , proofCoefficientEvals
  , proofIndexEvals
  , proofSigmaEvals
  , proofWitnessEvals
  , proofZEvals
  )
import Pickles.Prove.Pure.Wrap
  ( WrapDeferredValuesInput
  , assembleWrapMainInput
  , wrapComputeDeferredValues
  )
import Pickles.Verify.Types (toPlonkMinimal)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import JS.BigInt as BigInt
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Data.Array as Array
import Partial.Unsafe (unsafePartial)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Pickles.Step.Main as MpvPadding
import Pickles.Prove.Step
  ( StepAdvice(..)
  , StepCompileResult
  , StepProveContext
  , StepProveResult
  , StepRule
  , preComputeStepDomainLog2
  , stepCompile
  , stepSolveAndProve
  ) as PProveStep
import Pickles.Prove.Verify (CompiledProof(..), Verifier, mkVerifier)
import Pickles.Util.Unique (newUnique)
import Data.Newtype (wrap)
import Pickles.Prove.Wrap
  ( WrapCompileResult
  , buildWrapAdvice
  , buildWrapMainConfigMulti
  , wrapCompile
  , wrapSolveAndProve
  )
import Pickles.Step.Prevs (class PrevValuesCarrier, class PrevsCarrier)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StatementIO(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Wrap.Slots (class PadSlots)
import Pickles.Dummy
  ( baseCaseDummies
  , computeDummySgValues
  , dummyIpaChallenges
  , wrapDomainLog2ForProofsVerified
  , wrapDummyUnfinalizedProof
  )
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, UnChecked(..))
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue)
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
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier inputVal outputVal m =
  BranchProver
    ( StepInputs prevsSpec inputVal prevsCarrier
      -> ExceptT ProveError m
           (CompiledProof mpv (StatementIO inputVal outputVal) outputVal Unit)
    )

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
  -> (Type -> Type)
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
  -> Constraint
class
  CompilableRulesSpec rs inputVal outputVal prevInputVal branches mpvMax slotsMax
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

-- | Nil instance is polymorphic in `slotsMax` — Phase 2b.31b step (b)
-- | adds `slotsMax` to the class head; the Nil case returns unit-shaped
-- | carriers regardless, so any `slotsMax` works.
instance
  CompilableRulesSpec RulesNil inputVal outputVal prevInputVal 0 mpvMax slotsMax Unit
    Unit
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
      restBranches mpvMax slotsMax restCarrier restStepCompileFns restCtxs
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
  -- Phase 2b.31c: outputSize derives from mpvMax (the wrap circuit's
  -- max), not the rule's mpv. Step PI is mpvMax-shaped (mirrors OCaml
  -- step.ml:783-787).
  , Mul mpvMax 32 unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , Reflectable ruleMpv Int
  ) =>
  CompilableRulesSpec
    (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
    inputVal outputVal prevInputVal
    branches
    mpvMax
    slotsMax
    ( Tuple
        ( RuleEntry prevsSpec ruleMpv 1 valCarrier inputVal carrier outputSize
            slotVKs
        )
        restCarrier
    )
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv 1 -> Effect PProveStep.StepCompileResult
        )
        restStepCompileFns
    )
    (Tuple (PProveStep.StepProveContext ruleMpv 1) restCtxs)
    (Tuple PProveStep.StepCompileResult restStepCompileResults)
    (Tuple Int restLog2s)
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv 1
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
      @mpvMax
      @slotsMax
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
          @mpvMax
          @slotsMax
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
      @mpvMax
      @slotsMax
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
        @mpvMax
        @slotsMax
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
          @mpvMax
          @slotsMax
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

class CompilableRulesSpec rs inputVal outputVal prevInputVal branches mpvMax slotsMax
        rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
        perBranchStepCompileResults selfStepDomainLog2sCarrier
        stepProveFnsCarrier
   <= CompilableRulesSpecShape rs inputVal outputVal prevInputVal branches mpvMax slotsMax
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
  -- |
  -- | Returns BOTH the per-branch step CompileResults AND the
  -- | per-branch selfStepDomainLog2s — the latter feeds into
  -- | `buildBranchProvers` (for runMultiProverBody's wrapDvInput).
  runMultiCompileFull
    :: CompileMultiConfig
    -> rulesCarrier
    -> Effect
         { stepResults :: perBranchStepCompileResults
         , log2s :: selfStepDomainLog2sCarrier
         }

  -- | Build per-branch `BranchProver` Tuple chain. Each closure runs
  -- | step solve+prove (via the rule's `stepProveFn`) and wrap
  -- | solve+prove with `whichBranch = branchIdx`.
  -- |
  -- | Args:
  -- |   * `branchIdx` — branch index of the head entry; top-level
  -- |     callers pass `0`. Cons body recurses with `idx + 1`.
  -- |   * `cfg` — shared CompileMultiConfig.
  -- |   * `wrapResult` — single shared wrap CompileResult.
  -- |   * `perBranchVec` — full Vector of `{ mpv, stepDomainLog2,
  -- |     stepVK }` (shared across all branches; same vector used
  -- |     at wrap compile time via `buildWrapMainConfigMulti`).
  -- |     Each closure rebuilds the wrap-side WrapMainConfig from
  -- |     this when invoked.
  -- |   * step results / log2s / rules carriers — per-branch Tuple
  -- |     chains walked in sync with the recursion.
  buildBranchProvers
    :: forall vecLen vecLenPred
     . Reflectable vecLen Int
    => Add 1 vecLenPred vecLen
    => Int
    -> CompileMultiConfig
    -> WrapCompileResult
    -> Vector vecLen
         { mpv :: Int
         , stepDomainLog2 :: Int
         , stepVK :: VerifierIndex VestaG StepField
         }
    -> perBranchStepCompileResults
    -> selfStepDomainLog2sCarrier
    -> rulesCarrier
    -> Effect proversCarrier

-- | Nil shape instance is polymorphic in `slotsMax` (parallels the
-- | structural Nil instance).
instance
  CompilableRulesSpecShape RulesNil inputVal outputVal prevInputVal 0 mpvMax
    slotsMax Unit Unit Unit Unit Unit Unit Unit
  where
  runMultiCompile _ _ _ = pure unit
  runMultiCompileFull _ _ = pure { stepResults: unit, log2s: unit }
  buildBranchProvers _ _ _ _ _ _ _ = pure unit

instance
  ( CompilableRulesSpecShape rest inputVal outputVal prevInputVal
      restBranches mpvMax slotsMax restCarrier restStepCompileFns restCtxs
      restStepCompileResults restLog2s restStepProveFns restProvers
  , CompilableSpec prevsSpec slotVKs prevsCarrier ruleMpv slots valCarrier
      carrier
  , PrevValuesCarrier prevsSpec valCarrier
  -- Phase 2b.24b: per-rule wrap+step constraints needed by
  -- runMultiProverBody, in scope for the Cons body's call.
  , CircuitGateConstructor StepField VestaG
  , CircuitGateConstructor WrapField PallasG
  , Reflectable ruleMpv Int
  , Reflectable pad Int
  , Reflectable outputSize Int
  , Add pad ruleMpv PaddedLength
  -- Phase 2b.31c: outputSize derives from mpvMax.
  , Reflectable mpvPad Int
  , MpvPadding.MpvPadding mpvPad ruleMpv mpvMax
  , Mul mpvMax 32 unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , PadSlots slots ruleMpv
  -- Phase 2b.31b step (b): wrap-stage constraints on `mpvMax`/`slotsMax`
  -- (the wrap circuit's wider shape). Step (a) ran the wrap stage at
  -- the rule's `ruleMpv`/`slots` shape (identity `PadProveDataMpv`);
  -- step (b) runs it at `mpvMax`/`slotsMax` and uses the general
  -- `PadProveDataMpv` instance to convert.
  , Reflectable mpvMax Int
  , Reflectable padMax Int
  , Add padMax mpvMax PaddedLength
  , Compare mpvMax 3 LT
  , Add mpvMax 45 totalBasesMax
  , Add 1 totalBasesMaxPred totalBasesMax
  , PadSlots slotsMax mpvMax
  , PadProveDataMpv ruleMpv slots mpvMax slotsMax
  , CircuitType StepField inputVal inputVar
  , CircuitType StepField outputVal outputVar
  , CircuitType StepField prevInputVal prevInputVar
  , CircuitType StepField carrier carrierFVar
  , CheckedType StepField (KimchiConstraint StepField) inputVar
  , CheckedType StepField (KimchiConstraint StepField) carrierFVar
  , CircuitType WrapField
      (slotsMax (Vector WrapIPARounds (F WrapField)))
      (slotsMax (Vector WrapIPARounds (FVar WrapField)))
  , CheckedType WrapField (KimchiConstraint WrapField)
      (slotsMax (Vector WrapIPARounds (FVar WrapField)))
  , CompilableRulesSpec
      (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
      inputVal outputVal prevInputVal branches mpvMax slotsMax
      ( Tuple
          ( RuleEntry prevsSpec ruleMpv 1 valCarrier inputVal carrier outputSize
              slotVKs
          )
          restCarrier
      )
      ( Tuple
          ( PProveStep.StepProveContext ruleMpv 1 -> Effect PProveStep.StepCompileResult
          )
          restStepCompileFns
      )
      (Tuple (PProveStep.StepProveContext ruleMpv 1) restCtxs)
      (Tuple PProveStep.StepCompileResult restStepCompileResults)
      (Tuple Int restLog2s)
      ( Tuple
          ( PProveStep.StepProveContext ruleMpv 1
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
    branches mpvMax slotsMax
    ( Tuple
        ( RuleEntry prevsSpec ruleMpv 1 valCarrier inputVal carrier outputSize
            slotVKs
        )
        restCarrier
    )
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv 1 -> Effect PProveStep.StepCompileResult
        )
        restStepCompileFns
    )
    (Tuple (PProveStep.StepProveContext ruleMpv 1) restCtxs)
    (Tuple PProveStep.StepCompileResult restStepCompileResults)
    (Tuple Int restLog2s)
    ( Tuple
        ( PProveStep.StepProveContext ruleMpv 1
          -> PProveStep.StepCompileResult
          -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
               inputVal ruleMpv carrier valCarrier
          -> ExceptT EvaluationError Effect
               (PProveStep.StepProveResult outputSize)
        )
        restStepProveFns
    )
    -- Phase 2b.28: BranchProver is a NEWTYPE (was an alias).
    -- PS treats newtypes as nominally rigid — instance head sees
    -- a saturated type constructor, not an unfolded function
    -- type. Dispatch resolves cleanly; instance head stays terse.
    ( Tuple
        ( BranchProver prevsSpec ruleMpv prevsCarrier inputVal outputVal Effect
        )
        restProvers
    )
  where
  runMultiCompile cfg (Tuple log2 restLog2s) (Tuple (RuleEntry r) restEntries) = do
    let
      -- TODO Commit F: replace Vector 1 with the full
      -- `Vector branches Int` of all branches' step domain log2s for
      -- multi-rule Self-prev Pseudo dispatch. Currently each branch
      -- only sees its own log2 — circuit emits single-domain dispatch.
      ctx = buildStepProveCtx @prevsSpec cfg r.slotVKs (log2 :< Vector.nil)
    headResult <- r.stepCompileFn ctx
    tailResults <- runMultiCompile
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @mpvMax @slotsMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      cfg
      restLog2s
      restEntries
    pure (Tuple headResult tailResults)
  runMultiCompileFull cfg (Tuple (RuleEntry r) restEntries) = do
    let
      -- TODO Commit F: pre-pass over all branches to collect Vector
      -- branches Int, then compile each branch with the full vector.
      -- Currently sequential: each branch sees only its own log2.
      placeholderCtx =
        buildStepProveCtx @prevsSpec cfg r.slotVKs (20 :< Vector.nil)
    selfStepDomainLog2 <- r.preComputeStepDomainLog2Fn placeholderCtx
    let
      realCtx = buildStepProveCtx @prevsSpec cfg r.slotVKs
        (selfStepDomainLog2 :< Vector.nil)
    headResult <- r.stepCompileFn realCtx
    tail <- runMultiCompileFull
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @mpvMax @slotsMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      cfg
      restEntries
    pure
      { stepResults: Tuple headResult tail.stepResults
      , log2s: Tuple selfStepDomainLog2 tail.log2s
      }
  buildBranchProvers branchIdx cfg wrapResult perBranchVec
    (Tuple headStepCR restStepResults)
    (Tuple headLog2 restLog2s)
    (Tuple headEntry restEntries) = do
    let
      thisBranch = branchIdx
      headProver = BranchProver \stepInputs ->
        runMultiProverBody
          @prevsSpec
          @ruleMpv
          @slots
          @valCarrier
          @carrier
          @inputVal
          @inputVar
          @outputVal
          @outputVar
          @prevInputVal
          @prevInputVar
          -- Phase 2b.31b step (b): pass the wrap circuit's
          -- `mpvMax`/`slotsMax` (from the class instance head). For
          -- single-rule callers `ruleMpv = mpvMax` and `slots =
          -- slotsMax`, so the identity `PadProveDataMpv` instance
          -- fires (witness byte-identical with single-rule path).
          -- For multi-rule callers with mismatched shapes, the
          -- general instance fires and front-pads `proveData` to the
          -- wrap circuit's wider shape via `Dummy.*` values.
          @mpvMax
          @slotsMax
          @mpvPad
          thisBranch
          cfg
          wrapResult
          perBranchVec
          headStepCR
          headLog2
          headEntry
          stepInputs
    restProvers <- buildBranchProvers
      @rest @inputVal @outputVal @prevInputVal
      @restBranches @mpvMax @slotsMax
      @restCarrier @restStepCompileFns @restCtxs
      @restStepCompileResults @restLog2s @restStepProveFns @restProvers
      (branchIdx + 1)
      cfg
      wrapResult
      perBranchVec
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
  -> Int
  -> Type
  -> Type
  -> Type
  -> Int
  -> Type
  -> Type
data RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize slotVKs = RuleEntry
  { -- | Pre-pass: takes a placeholder `StepProveContext mpv` (built
    -- | with OCaml `rough_domains` log2=20) and returns the actual
    -- | `selfStepDomainLog2` derived by counting gates in a one-shot
    -- | constraint-system build. Phase 2b.15 — analog of OCaml's
    -- | `Fix_domains.domains` per-rule.
    --
    -- | `nd` is the compilation-wide multi-domain count. For
    -- | single-rule callers this is 1; for multi-rule (compileMulti)
    -- | it's the proof-system's `branches` count, used for Pseudo
    -- | dispatch over Self-prev step domains in
    -- | `finalizeOtherProofCircuit`.
    preComputeStepDomainLog2Fn ::
      PProveStep.StepProveContext mpv nd -> Effect Int
  , stepCompileFn ::
      PProveStep.StepProveContext mpv nd -> Effect PProveStep.StepCompileResult
  , stepProveFn ::
      PProveStep.StepProveContext mpv nd
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
  :: forall @prevsSpec @mpv @mpvMax @mpvPad @nd _nd @outputSize @valCarrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar @slotVKs
       carrier carrierVar pad unfsTotal digestPlusUnfs
   . CircuitGateConstructor StepField VestaG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Add 1 _nd nd
  => Compare 0 nd LT
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => MpvPadding.MpvPadding mpvPad mpv mpvMax
  => Mul mpvMax 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
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
  -> Effect (RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize slotVKs)
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
        @mpvMax
        @mpvPad
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
        @mpvMax
        @mpvPad
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
        @mpvMax
        @mpvPad
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
  :: forall @prevsSpec @nd _nd slotVKs prevsCarrier mpv slots valCarrier carrier
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => Add 1 _nd nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => CompileMultiConfig
  -> slotVKs
  -> Vector nd Int
  -> PProveStep.StepProveContext mpv nd
buildStepProveCtx cfg slotVKs selfStepDomainLog2s =
  let
    perRuleCfg =
      { srs: cfg.srs
      , perSlotImportedVKs: slotVKs
      , debug: cfg.debug
      , wrapDomainOverride: cfg.wrapDomainOverride
      }
    shape = shapeCompileData @prevsSpec perRuleCfg selfStepDomainLog2s
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
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal branches mpvMax slots
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
  { stepResults } <- runMultiCompileFull
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @branches
    @mpvMax
    @slots
    cfg
    rules
  let
    perBranchVec = buildWrapPerBranchVec
      @rs
      @inputVal
      @outputVal
      @prevInputVal
      @branches
      @mpvMax
      @slots
      stepResults
  wrapResult <- wrapCompile @branches @slots
    { wrapMainConfig:
        buildWrapMainConfigMulti @branches cfg.srs.vestaSrs
          { perBranch: perBranchVec }
    , crs: cfg.srs.pallasSrs
    }
  pure { stepResults, wrapResult, perBranchVec }

--------------------------------------------------------------------------------
-- runMultiProverBody — Phase 2b.24 skeleton: per-branch prover body
-- analog of single-rule `Pickles.Prove.Compile.runProverBody`.
--
-- The full implementation will mirror runProverBody (Compile.purs:1466+):
--   1. mkStepAdvice @prevsSpec cfg stepCR wrapResult appInput prevs
--   2. shapeProveData @prevsSpec cfg wrapResult sideInfo prevs
--   3. stepProveFn ctx stepCR stepAdvice  (was stepSolveAndProve in single-rule)
--   4. compute step oracles + allEvals
--   5. wrapComputeDeferredValues
--   6. wrapSolveAndProve with `whichBranch: F (fromInt branchIdx)`
--   7. package CompiledProof
--
-- Phase 2b.24a (this commit): notImplemented body. Phase 2b.24b+ will
-- fill in the steps incrementally, each verified by typechecking.
--
-- Why a top-level function (vs class method): the body uses many
-- per-rule type vars + constraints, and writing it inside a class
-- method body forces all those vars/constraints onto the class
-- instance head — which we just split apart in Phase 2b.20 to
-- minimize. Keeping it top-level localizes the constraints to this
-- function.
--
-- The class method `buildBranchProvers` calls this at each per-branch
-- closure, passing the captured `branchIdx` + per-branch step result.
--------------------------------------------------------------------------------

runMultiProverBody
  :: forall @prevsSpec slotVKs prevsCarrier @mpv @slots @valCarrier @carrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
       @mpvMax @slotsMax @mpvPad
       branches branchesPred
       pad unfsTotal digestPlusUnfs outputSize carrierFVar
       padMax totalBasesMax totalBasesMaxPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => PrevValuesCarrier prevsSpec valCarrier
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Add 1 branchesPred branches
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable mpvPad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => MpvPadding.MpvPadding mpvPad mpv mpvMax
  => Mul mpvMax 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  -- Step-half constraints reference the rule's own `mpv`. The wrap
  -- circuit operates at the (possibly wider) `mpvMax`/`slotsMax`
  -- shape; constraints below mirror that — they are independent of
  -- the rule's `mpv` / `slots`.
  => Reflectable mpvMax Int
  => Reflectable padMax Int
  => Add padMax mpvMax PaddedLength
  => Compare mpvMax 3 LT
  => Add mpvMax 45 totalBasesMax
  => Add 1 totalBasesMaxPred totalBasesMax
  => PadSlots slotsMax mpvMax
  => PadProveDataMpv mpv slots mpvMax slotsMax
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => CheckedType StepField (KimchiConstraint StepField) carrierFVar
  => CircuitType WrapField
       (slotsMax (Vector WrapIPARounds (F WrapField)))
       (slotsMax (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slotsMax (Vector WrapIPARounds (FVar WrapField)))
  => Int
  -- ^ branchIdx — baked into the wrap statement's `whichBranch`.
  -> CompileMultiConfig
  -> WrapCompileResult
  -> Vector branches
       { mpv :: Int
       , stepDomainLog2 :: Int
       , stepVK :: VerifierIndex VestaG StepField
       }
  -- ^ shared per-branch wrap config inputs (same vector used at
  --   wrap compile time via `buildWrapMainConfigMulti`); the wrap
  --   solver here rebuilds the same `WrapMainConfig` from this.
  -> PProveStep.StepCompileResult
  -- ^ this branch's step compile result
  -> Int
  -- ^ this branch's selfStepDomainLog2 (from the pre-pass)
  -> RuleEntry prevsSpec mpv 1 valCarrier inputVal carrier outputSize slotVKs
  -> StepInputs prevsSpec inputVal prevsCarrier
  -> ExceptT ProveError Effect
       (CompiledProof mpv (StatementIO inputVal outputVal) outputVal Unit)
runMultiProverBody _branchIdx cfg wrapResult perBranchVec
  stepCR selfStepDomainLog2
  (RuleEntry r) { appInput, prevs } = do
  -- Phase 2b.24c: step half — mkStepAdvice + shapeProveData +
  -- step solve+prove. Wrap half (oracles, deferred values, wrap
  -- solver) deferred to Phase 2b.24d.
  let
    perRuleCfg =
      { srs: cfg.srs
      , perSlotImportedVKs: r.slotVKs
      , debug: cfg.debug
      , wrapDomainOverride: cfg.wrapDomainOverride
      }
    -- TODO Commit F: pass the full
    --   `Vector branches Int` (= `map _.stepDomainLog2 perBranchVec`)
    -- to drive multi-domain Pseudo dispatch in
    -- `finalizeOtherProofCircuit`. Currently Vector 1 with the
    -- branch's own step domain — circuit emits single-domain
    -- dispatch even for multi-rule callers (TwoPhaseChain b1_step
    -- still has the 4-Generic-gate delta).
    selfDomainsForShape :: Vector 1 Int
    selfDomainsForShape = selfStepDomainLog2 :< Vector.nil
    shape = shapeCompileData @prevsSpec perRuleCfg selfDomainsForShape

  { stepAdvice, challengePolynomialCommitments, baseCaseWrapPublicInputs } <-
    liftEffect $ mkStepAdvice @prevsSpec perRuleCfg stepCR wrapResult appInput
      prevs

  let
    PProveStep.StepAdvice sa = stepAdvice
    proveDataSideInfo :: ShapeProveSideInfo mpv
    proveDataSideInfo =
      { challengePolynomialCommitments
      , unfinalizedSlots: sa.publicUnfinalizedProofs
      , baseCaseWrapPublicInputs
      }
    proveData = shapeProveData @prevsSpec perRuleCfg wrapResult
      proveDataSideInfo
      prevs

    -- Pad rule's mpv/slots-shaped proveData to the wrap circuit's
    -- mpvMax/slotsMax shape. Identity for single-rule callers
    -- (mpv = mpvMax, slots = slotsMax); the general
    -- `PadProveDataMpv` instance front-pads with dummies for
    -- multi-rule callers where the rule's mpv < wrap's mpvMax.
    --
    -- Dummies sized at the wrap circuit's `mpvMax` mirror OCaml
    -- `step.ml:736-770`'s `extend_front ... Unfinalized.dummy` and
    -- the surrounding per-prev fields' analogous front-pad calls.
    outerMpvMax = reflectType (Proxy @mpvMax)
    bcdMax = baseCaseDummies { maxProofsVerified: outerMpvMax }
    dummySgsMax = computeDummySgValues bcdMax cfg.srs.pallasSrs cfg.srs.vestaSrs
    -- `ipa.step.sg :: AffinePoint WrapField` is what `prevSgs` /
    -- `prevStepAccs` consume (the prev WRAP proof's IPA opening sg
    -- lives on Pallas, with WrapField coords). `ipa.wrap.sg ::
    -- AffinePoint StepField` lives on Vesta with StepField coords
    -- — used for `kimchiPrevEntries.sgX`/`sgY`.
    dummyStepSgInWrapField = dummySgsMax.ipa.step.sg -- AffinePoint WrapField
    dummyWrapSgInStepField = dummySgsMax.ipa.wrap.sg -- AffinePoint StepField

    -- Flatten `wrapDummyUnfinalizedProof`'s nested
    -- `UnfinalizedProof { deferredValues, … }` shape into the flat
    -- `PerProofUnfinalized` record `ShapeProveData` carries. Both
    -- sides are already wrap-field (`Type2 (F WrapField)` /
    -- `F WrapField`) — no cross-field coerce needed.
    dummyUnfRaw = wrapDummyUnfinalizedProof bcdMax
    dummyUnfDv = dummyUnfRaw.deferredValues
    dummyPlonk = dummyUnfDv.plonk
    dummyPpu :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean
    dummyPpu = PerProofUnfinalized
      { combinedInnerProduct: dummyUnfDv.combinedInnerProduct
      , b: dummyUnfDv.b
      , zetaToSrsLength: dummyPlonk.zetaToSrsLength
      , zetaToDomainSize: dummyPlonk.zetaToDomainSize
      , perm: dummyPlonk.perm
      , spongeDigest: dummyUnfRaw.spongeDigestBeforeEvaluations
      , beta: UnChecked dummyPlonk.beta
      , gamma: UnChecked dummyPlonk.gamma
      , alpha: UnChecked dummyPlonk.alpha
      , zeta: UnChecked dummyPlonk.zeta
      , xi: UnChecked dummyUnfDv.xi
      , bulletproofChallenges: map UnChecked dummyUnfDv.bulletproofChallenges
      , shouldFinalize: dummyUnfRaw.shouldFinalize
      }

    -- `StepAllEvals (F WrapField)` lifted from `bcd.dummyEvals`
    -- (`AllEvals WrapField`). Mirrors OCaml `dummy.ml:7-20`'s
    -- `Dummy.evals` — every field, including `publicEvals`, is
    -- populated by `Ro.tock ()` draws (NOT zero placeholders). The
    -- `Ro` stream is already advanced consistently with OCaml via
    -- `baseCaseDummies { maxProofsVerified: mpvMax }`.
    de = bcdMax.dummyEvals
    pe pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
    dummyPrevEvalsMax :: StepAllEvals (F WrapField)
    dummyPrevEvalsMax = StepAllEvals
      { ftEval1: F de.ftEval1
      , publicEvals: pe de.publicEvals
      , zEvals: pe de.zEvals
      , witnessEvals: map pe de.witnessEvals
      , coeffEvals: map pe de.coeffEvals
      , sigmaEvals: map pe de.sigmaEvals
      , indexEvals: map pe de.indexEvals
      }

    padDummies :: PadProveDataDummies
    padDummies =
      { dummyPrevSg: dummyStepSgInWrapField
      , dummyPrevStepChals: dummyIpaChallenges.stepExpanded
      , dummyMsgWrapChal: dummyIpaChallenges.wrapExpanded
      , dummyPrevUnfinalizedProof: dummyPpu
      , dummyPrevStepAcc:
          WeierstrassAffinePoint
            { x: F dummyStepSgInWrapField.x, y: F dummyStepSgInWrapField.y }
      , dummyPrevEvals: dummyPrevEvalsMax
      -- OCaml `wrap.ml:412-414` pads `wrap_domain_indices` with
      -- `Tock.Field.one` (NOT zero) when actualProofsVerified <
      -- maxProofsVerified. This matches the wrap circuit's
      -- expectation for `branch_data.domain` of a dummy slot
      -- (encodes `Pow_2_roots_of_unity 14` = the wrap circuit's own
      -- domain, all_possible_domains[1]).
      , dummyPrevWrapDomainIdx: F one
      , dummyKimchiPrevEntry:
          { sgX: dummyWrapSgInStepField.x
          , sgY: dummyWrapSgInStepField.y
          , challenges: dummyIpaChallenges.wrapExpanded
          }
      , dummySlotChal: map F dummyIpaChallenges.wrapExpanded
      }

    proveDataMax :: ShapeProveData mpvMax slotsMax
    proveDataMax = padShapeProveData padDummies proveData

  stepResult <- r.stepProveFn shape.stepProveCtx stepCR stepAdvice

  let
    -- Phase 2b.24e: assemble FFI-shaped `prevChallenges` for the
    -- step proof's oracles. Same shape as single-rule
    -- runProverBody (Compile.purs:1502-1508).
    stepOraclesPrevChals = Vector.toUnfoldable $
      Vector.zipWith
        ( \sg chals ->
            { sgX: sg.x
            , sgY: sg.y
            , challenges: Vector.toUnfoldable chals
            }
        )
        proveData.prevSgs
        proveData.prevStepChallenges

    stepOracles = pallasProofOracles stepCR.verifierIndex
      { proof: stepResult.proof
      , publicInput: stepResult.publicInputs
      , prevChallenges: stepOraclesPrevChals
      }

    -- Phase 2b.24f: AllEvals struct, mirroring single-rule
    -- runProverBody (Compile.purs:1517-1529).
    allEvals :: AllEvals StepField
    allEvals =
      { ftEval1: stepOracles.ftEval1
      , publicEvals:
          { zeta: stepOracles.publicEvalZeta
          , omegaTimesZeta: stepOracles.publicEvalZetaOmega
          }
      , zEvals: proofZEvals stepResult.proof
      , witnessEvals: proofWitnessEvals stepResult.proof
      , coeffEvals: proofCoefficientEvals stepResult.proof
      , sigmaEvals: proofSigmaEvals stepResult.proof
      , indexEvals: proofIndexEvals stepResult.proof
      }

    -- Phase 2b.24g: WrapDeferredValuesInput, mirroring single-rule
    -- runProverBody (Compile.purs:1531-1557).
    outerMpv = reflectType (Proxy @mpv)

    proofsVerifiedMask :: Vector 2 Boolean
    proofsVerifiedMask = (outerMpv >= 2) :< (outerMpv >= 1) :< Vector.nil

    wrapDvInput :: WrapDeferredValuesInput mpv
    wrapDvInput =
      { proof: stepResult.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: stepResult.publicInputs
      , allEvals
      , pEval0Chunks: [ stepOracles.publicEvalZeta ]
      , domainLog2: selfStepDomainLog2
      , zkRows: 3
      , srsLengthLog2: 16
      , generator: (domainGenerator selfStepDomainLog2 :: StepField)
      , shifts: (domainShifts selfStepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: permutationVanishingPolynomial
          { domainLog2: selfStepDomainLog2
          , zkRows: 3
          , pt: stepOracles.zeta
          }
      , omegaForLagrange: \_ -> one
      , endo:
          let EndoScalar e = endoScalar :: EndoScalar StepField in e
      , linearizationPoly: Linearization.pallas
      , prevSgs: proveData.prevSgs
      , prevChallenges: proveData.prevStepChallenges
      , proofsVerifiedMask
      }

    _wrapDv = wrapComputeDeferredValues wrapDvInput

    -- Phase 2b.24h: msgStep / stepProofSg / msgWrap + paddings.
    -- Mirrors Compile.purs:1568-1612.
    msgStep :: StepField
    msgStep = unsafePartial $ fromJust $
      Array.index stepResult.publicInputs (outerMpv * 32)

    stepProofSg :: AffinePoint WrapField
    stepProofSg = pallasProofOpeningSg stepResult.proof

    dummyWrapExpanded :: Vector WrapIPARounds WrapField
    dummyWrapExpanded = dummyIpaChallenges.wrapExpanded

    -- Phase 2b.31c: use the wrap circuit's `mpvMax`-derived bcd (same
    -- one feeding `padDummies` above) so the front-pad dummies and
    -- the `padShapeProveData` dummies share an Ro stream. Single-rule
    -- callers have `mpv = mpvMax` so this binds the same value as
    -- before — no witness regression. Multi-rule callers (e.g.
    -- TwoPhaseChain b0 with mpv=0, mpvMax=1) now match — was using
    -- bcd at rule's mpv vs. bcdMax at mpvMax, leaving the wrap
    -- circuit's permutation argument open.
    dummyKimchiEntry
      :: { sgX :: StepField
         , sgY :: StepField
         , challenges :: Vector WrapIPARounds WrapField
         }
    dummyKimchiEntry =
      { sgX: dummyWrapSgInStepField.x
      , sgY: dummyWrapSgInStepField.y
      , challenges: dummyIpaChallenges.wrapExpanded
      }

    msgWrapPadded :: Vector PaddedLength (Vector WrapIPARounds WrapField)
    msgWrapPadded =
      Vector.append (Vector.replicate @padMax dummyWrapExpanded)
        proveDataMax.msgWrapChallenges

    _kimchiPrevPadded
      :: Vector PaddedLength
           { sgX :: StepField
           , sgY :: StepField
           , challenges :: Vector WrapIPARounds WrapField
           }
    _kimchiPrevPadded =
      Vector.append (Vector.replicate @padMax dummyKimchiEntry)
        proveDataMax.kimchiPrevEntries

    msgWrap :: WrapField
    msgWrap = hashMessagesForNextWrapProofPureGeneral
      { sg: stepProofSg
      , paddedChallenges: msgWrapPadded
      }

    wrapDv = wrapComputeDeferredValues wrapDvInput

    -- Phase 2b.24i: wrap statement+advice (with whichBranch baked
    -- per-branch via `F (fromInt branchIdx)`), wrap solver context.
    -- Mirrors Compile.purs:1614-1637, with two changes:
    --   * buildWrapMainConfigMulti (multi-branch) instead of
    --     single-rule buildWrapMainConfig.
    --   * whichBranch parameterized from the outer branchIdx.
    wrapCtx =
      { wrapMainConfig:
          buildWrapMainConfigMulti @branches cfg.srs.vestaSrs
            { perBranch: perBranchVec
            }
      , crs: cfg.srs.pallasSrs
      , publicInput: assembleWrapMainInput
          { deferredValues: wrapDv
          , messagesForNextStepProofDigest: msgStep
          , messagesForNextWrapProofDigest: msgWrap
          }
      , advice: buildWrapAdvice
          { stepProof: stepResult.proof
          , whichBranch: F (fromBigInt (BigInt.fromInt _branchIdx) :: WrapField)
          , prevUnfinalizedProofs: proveDataMax.prevUnfinalizedProofs
          , prevMessagesForNextStepProofHash:
              F (fromBigInt (toBigInt msgStep) :: WrapField)
          , prevStepAccs: proveDataMax.prevStepAccs
          , prevOldBpChals: proveDataMax.slotsValue
          , prevEvals: proveDataMax.prevEvals
          , prevWrapDomainIndices: proveDataMax.prevWrapDomainIndices
          }
      , debug: cfg.debug
      , kimchiPrevChallenges: _kimchiPrevPadded
      }

  wrapProveResult <- wrapSolveAndProve @branches @slotsMax wrapCtx wrapResult

  let
    -- Recover the rule's user-defined `publicOutput` from
    -- stepResult.userPublicOutputFields (populated post-solve via
    -- the stepMain Ref). NOT stepResult.publicOutputs (which is
    -- the kimchi public-output vector = digest+unfinalized+
    -- wrap-msgs).
    publicOutput =
      fieldsToValue @StepField stepResult.userPublicOutputFields

  pure $ CompiledProof
    { statement: StatementIO { input: appInput, output: publicOutput }
    , publicOutput
    , auxiliaryOutput: unit
    , wrapProof: wrapProveResult.proof
    , rawPlonk: toPlonkMinimal wrapDv.plonk
    , rawBulletproofChallenges: wrapDv.bulletproofPrechallenges
    , branchData: wrapDv.branchData
    , spongeDigestBeforeEvaluations: wrapDv.spongeDigestBeforeEvaluations
    , prevEvals: allEvals
    , pEval0Chunks: [ stepOracles.publicEvalZeta ]
    , oldBulletproofChallenges: proveData.prevStepChallenges
    , challengePolynomialCommitment: stepProofSg
    , messagesForNextStepProofDigest: msgStep
    , messagesForNextWrapProofDigest: msgWrap
    , msgWrapChallenges: proveData.msgWrapChallenges
    , outerStepChalPolyComms:
        map (\e -> { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
    , wrapDvInput
    , wrapDv
    }

compileMulti
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
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal branches mpvMax slots
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
  => Compare 0 branches LT
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
       ( MultiOutput
           proversCarrier
           perBranchStepCompileResults
           mpvMax
           inputVal
           outputVal
           Unit
       )
compileMulti cfg rules = do
  -- Step 1: per-rule pre-pass + step compile.
  { stepResults, log2s } <- runMultiCompileFull
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @branches
    @mpvMax
    @slots
    cfg
    rules

  let
    perBranchVec = buildWrapPerBranchVec
      @rs
      @inputVal
      @outputVal
      @prevInputVal
      @branches
      @mpvMax
      @slots
      stepResults

  -- Step 2: shared wrap compile across all branches.
  wrapResult <- wrapCompile @branches @slots
    { wrapMainConfig:
        buildWrapMainConfigMulti @branches cfg.srs.vestaSrs
          { perBranch: perBranchVec }
    , crs: cfg.srs.pallasSrs
    }

  -- Step 3: build per-branch BranchProver closures (each captures its
  -- branchIdx for `whichBranch` baking in the wrap statement).
  provers <- buildBranchProvers
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @branches
    @mpvMax
    @slots
    0
    cfg
    wrapResult
    perBranchVec
    stepResults
    log2s
    rules

  -- Step 4: shared verifier + tag.
  unique <- newUnique
  let
    -- Placeholder: uses the pre-pass log2 of the FIRST branch as
    -- the verifier's stepDomainLog2. Multi-branch verification will
    -- need a per-branch shape; deferred to a Verifier refactor.
    firstBranchStepDomainLog2 =
      (Vector.uncons perBranchVec).head.stepDomainLog2

    -- Wrap circuit's own domain log2 (= wrap_domains[mpvMax]).
    -- Used by the verifier for wrap-side proof validation; not
    -- consumed by the wrap circuit body anymore (the wrap circuit
    -- now picks per-branch lagrange bases from `perBranchLagrangeAt`,
    -- mirroring OCaml `lagrange_with_correction`).
    wrapDomainLog2Out =
      wrapDomainLog2ForProofsVerified (reflectType (Proxy :: Proxy mpvMax))

    verifier :: Verifier
    verifier = mkVerifier
      { wrapVK: wrapResult.verifierIndex
      , vestaSrs: cfg.srs.vestaSrs
      , stepDomainLog2: firstBranchStepDomainLog2
      }

  pure
    { provers
    , tag: wrap { unique, verifier }
    , verifier
    , vks:
        { wrap: wrapResult
        , perBranchStep: stepResults
        , wrapDomainLog2: wrapDomainLog2Out
        }
    , perBranchVKs: unit
    }

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
