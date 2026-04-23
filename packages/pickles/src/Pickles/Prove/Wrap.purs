-- | Prover-side infrastructure for `Pickles.Wrap.Main.wrapMain`.
-- |
-- | While `Pickles.Prove.Pure.Wrap` covers the **pure** pieces of the
-- | wrap prover (deferred-values derivation + statement assembly), this
-- | module provides the **effectful** glue that feeds `wrapMain`'s
-- | `Req.*` advice during witness generation:
-- |
-- | * `WrapAdvice` — a record holding all 8 advice pieces (one per
-- |   OCaml `Req.*` request) with concrete, already-computed values.
-- | * `WrapProverT` — a `ReaderT` transformer serving `WrapAdvice` to
-- |   the circuit body. Instances below implement `WrapWitnessM` so
-- |   the `wrapMain` circuit body can `ask` for each advice piece.
-- | * `runWrapProverT` — runner that supplies the advice and unwraps
-- |   to the base monad (`Effect`).
-- |
-- | This replaces the stub `WrapMainProverM` that lived in
-- | `Test.Pickles.TestContext`; it lives in library code so the new
-- | wrap-prover pipeline (stages A/B/C in the port plan) can build on
-- | it without leaning on test-only scaffolding.
module Pickles.Prove.Wrap
  ( WrapAdvice
  , WrapProverT(..)
  , runWrapProverT
  , BuildWrapAdviceInput
  , buildWrapAdvice
  , WrapProveContext
  , WrapCompileContext
  , WrapCompileResult
  , WrapProveResult
  , wrapCompile
  , wrapSolveAndProve
  , extractStepVKComms
  , stepVkForCircuit
  , buildWrapMainConfig
  ) where

import Prelude

import Control.Monad.Except (ExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Map (Map)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.ProofFFI (Proof, pallasProofCommitments, pallasProofOpeningDelta, pallasProofOpeningLrVec, pallasProofOpeningSg, pallasProofOpeningZ1, pallasProofOpeningZ2, pallasSrsBlindingGenerator, pallasSrsLagrangeCommitmentAt, pallasVerifierIndexCommitments, tCommVec, vestaCreateProofWithPrev)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Types (PaddedLength, PerProofUnfinalized, StepAllEvals, StepField, StepIPARounds, WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked)
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Slots (class PadSlots)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.DSL (class CheckedType, F(..), FVar, const_)
import Snarky.Circuit.Kimchi (Type1, Type2, toShifted)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), endoBase)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Private witness data the wrap prover supplies to `wrapMain`. One
-- | field per `Req.*` request, in the same order `wrap_main.ml`
-- | consumes them.
-- |
-- | Type parameters mirror `WrapWitnessM`:
-- |
-- | * `mpv` — max_proofs_verified (varies per compile: N0, N1, or N2).
-- | * `slots` — the slot-list shape, a `Type -> Type` from
-- |   `Pickles.Wrap.Slots` (`NoSlots`, `Slots1 w`, or `Slots2 w0 w1`).
-- |
-- | The commitment curve is pinned to `VestaG` (the Step proof's
-- | commitment curve) and the field to `WrapField` (= `Vesta.BaseField`
-- | = the native field of the wrap circuit).
type WrapAdvice (mpv :: Int) (slots :: Type -> Type) =
  { whichBranch :: F WrapField
  , wrapProofState ::
      WrapPrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
  , stepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  , oldBpChals :: slots (Vector WrapIPARounds (F WrapField))
  , evals :: Vector mpv (StepAllEvals (F WrapField))
  , wrapDomainIndices :: Vector mpv (F WrapField)
  , openingProof ::
      WrapProofOpening
        StepIPARounds
        (WeierstrassAffinePoint VestaG (F WrapField))
        (Type1 (F WrapField))
  , messages :: WrapProofMessages (WeierstrassAffinePoint VestaG (F WrapField))
  }

-- | ReaderT transformer carrying a `WrapAdvice` over a base monad.
-- |
-- | At compile time the base monad is typically `Effect` (matching how
-- | `compile` and the witness-generation path work across the rest of
-- | the pickles package). The `branches` parameter is a phantom — it's
-- | only there so the `WrapWitnessM` instance can pin it for the
-- | caller; the ReaderT body never inspects it.
newtype WrapProverT
  :: Int
  -> Int
  -> (Type -> Type)
  -> (Type -> Type)
  -> Type
  -> Type
newtype WrapProverT
  branches
  mpv
  slots
  m
  a = WrapProverT (ReaderT (WrapAdvice mpv slots) m a)

derive instance Newtype (WrapProverT branches mpv slots m a) _
derive newtype instance Functor m => Functor (WrapProverT branches mpv slots m)
derive newtype instance Apply m => Apply (WrapProverT branches mpv slots m)
derive newtype instance Applicative m => Applicative (WrapProverT branches mpv slots m)
derive newtype instance Bind m => Bind (WrapProverT branches mpv slots m)
derive newtype instance Monad m => Monad (WrapProverT branches mpv slots m)

-- | Supply the advice record and run the prover computation in the
-- | base monad.
runWrapProverT
  :: forall branches mpv slots m a
   . WrapAdvice mpv slots
  -> WrapProverT branches mpv slots m a
  -> m a
runWrapProverT advice (WrapProverT m) = runReaderT m advice

-- | `WrapWitnessM` instance serving each advice piece from the
-- | reader. One method per `Req.*` request; all of them are plain
-- | record projections via `ask`.
instance
  ( Monad m
  , Reflectable branches Int
  , Reflectable mpv Int
  , PadSlots slots mpv
  ) =>
  WrapWitnessM
    branches
    mpv
    slots
    VestaG
    WrapField
    (WrapProverT branches mpv slots m) where
  getWhichBranch _ = WrapProverT $ map _.whichBranch ask
  getWrapProofState _ = WrapProverT $ map _.wrapProofState ask
  getStepAccs _ = WrapProverT $ map _.stepAccs ask
  getOldBulletproofChallenges _ = WrapProverT $ map _.oldBpChals ask
  getEvals _ = WrapProverT $ map _.evals ask
  getWrapDomainIndices _ = WrapProverT $ map _.wrapDomainIndices ask
  getOpeningProof _ = WrapProverT $ map _.openingProof ask
  getMessages _ = WrapProverT $ map _.messages ask

--------------------------------------------------------------------------------
-- Advice builder
--
-- `buildWrapAdvice` assembles a `WrapAdvice` record from a step proof
-- plus the surrounding data the pickles framework carries alongside
-- it. Split of responsibilities:
--
-- * Advice pieces derivable **from the step proof itself** (its kimchi
--   in-memory form) are extracted here via the `pallas*` FFIs —
--   `messages` and `openingProof`.
-- * Advice pieces that come from the step proof's **public input**
--   (which the caller decoded upstream) are threaded through as
--   direct parameters — `prevUnfinalizedProofs`,
--   `prevMessagesForNextStepProofHash`. These are effectively the
--   step proof's own committed `Types.Step.Statement` contents.
-- * Advice pieces that come from the step prover's **private state**
--   (= *not* committed by the step proof's public input) are also
--   direct parameters — `prevStepAccs`, `prevOldBpChals`, `prevEvals`,
--   `prevWrapDomainIndices`. OCaml's `wrap.ml` receives these via the
--   `P.Base.Step.t` record that the step prover hands to the wrap
--   prover; we do the same.
-- * `whichBranch` is a direct parameter (single-branch tests pass
--   zero; multi-branch callers select the active branch index).
--
-- Cross-field conversions:
--
-- * Step proof opening scalars `z1`/`z2` are `StepField` values; the
--   wrap statement stores them as `Type1 (F WrapField)`. We go
--   through the cross-field `Shifted (F StepField) (Type1 (F WrapField))`
--   instance.
-- * Step proof commitments are Vesta affine points with coordinates
--   in `Vesta.BaseField = WrapField`, so no cross-field conversion is
--   needed — `WeierstrassAffinePoint VestaG (F WrapField)` wraps
--   them directly.
--------------------------------------------------------------------------------

-- | Input record for `buildWrapAdvice`. Every field has a direct
-- | correspondence to how OCaml's `wrap.ml` assembles the same data
-- | for the wrap circuit handler.
type BuildWrapAdviceInput (mpv :: Int) (slots :: Type -> Type) =
  { -- | The step proof being wrapped (kimchi in-memory form).
    stepProof :: Proof Vesta.G StepField

  -- | Selected step-branch index. OCaml: `Req.Which_branch`.
  , whichBranch :: F WrapField

  -- | mpv unfinalized proofs decoded out of the step proof's public
  -- | input, in wrap-field Type2 form (same-field, not SplitField —
  -- | caller unpacks via `fromShifted`/`toShifted` if their decoded
  -- | statement uses SplitField).
  , prevUnfinalizedProofs ::
      Vector mpv
        ( PerProofUnfinalized
            WrapIPARounds
            (Type2 (F WrapField))
            (F WrapField)
            Boolean
        )

  -- | The step-field Poseidon digest that sits in the step proof's
  -- | public input under `messages_for_next_step_proof`. Already
  -- | cross-field coerced to `F WrapField` by the caller (= OCaml's
  -- | `Digest.Constant.of_tick_field`).
  , prevMessagesForNextStepProofHash :: F WrapField

  -- | The previous wrap proofs' step accumulators (Vesta affines with
  -- | wrap-field coords). Not in the step proof's public input —
  -- | pickles carries these as private prover state. For base case
  -- | supply dummy sgs.
  , prevStepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))

  -- | Heterogeneous prev wrap bp challenges, in `slots`-shaped form
  -- | (one of `NoSlots`, `Slots1 w`, `Slots2 w0 w1` from
  -- | `Pickles.Wrap.Slots`). Constructed via the smart constructors
  -- | `noSlots` / `slots1` / `slots2`.
  , prevOldBpChals :: slots (Vector WrapIPARounds (F WrapField))

  -- | Prev wrap proofs' polynomial evaluations (`StepAllEvals` per
  -- | proof, wrap-field scalars). OCaml's `prev_evals`.
  , prevEvals :: Vector mpv (StepAllEvals (F WrapField))

  -- | Domain indices per prev wrap proof (into `all_possible_domains`).
  , prevWrapDomainIndices :: Vector mpv (F WrapField)
  }

-- | `WeierstrassAffinePoint VestaG (F WrapField)` from a raw FFI
-- | `AffinePoint WrapField`.
mkVestaPt
  :: AffinePoint WrapField
  -> WeierstrassAffinePoint VestaG (F WrapField)
mkVestaPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

-- | Build the wrap-circuit advice record from the step proof + its
-- | surrounding pickles context. Pure: all FFI calls go through
-- | deterministic `pallas*` helpers exposed as non-effectful in
-- | `Pickles.ProofFFI`.
buildWrapAdvice
  :: forall mpv slots
   . BuildWrapAdviceInput mpv slots
  -> WrapAdvice mpv slots
buildWrapAdvice input =
  let
    -- ===== Req.Messages (step.ml commitments → wrap witness). =====
    --
    -- `pallasProofCommitments` returns wComm (Vector 15) + zComm
    -- (single) + tComm (Array). Length-pin tComm at 7 to match the
    -- `WrapProofMessages` shape.
    commits = pallasProofCommitments input.stepProof

    messagesOut :: WrapProofMessages (WeierstrassAffinePoint VestaG (F WrapField))
    messagesOut = WrapProofMessages
      { wComm: map mkVestaPt commits.wComm
      , zComm: mkVestaPt commits.zComm
      , tComm: map mkVestaPt (tCommVec commits)
      }

    -- ===== Req.Openings_proof. =====
    --
    -- Step proof's bulletproof opening: lr pairs (length StepIPARounds),
    -- delta / sg curve points, and z1/z2 scalars. The scalars are
    -- `StepField` values; cross-field `toShifted` packs them as
    -- `Type1 (F WrapField)` via the `Shifted (F StepField)
    -- (Type1 (F WrapField))` instance.
    lrVec
      :: Vector StepIPARounds
           { l :: WeierstrassAffinePoint VestaG (F WrapField)
           , r :: WeierstrassAffinePoint VestaG (F WrapField)
           }
    lrVec = map (\p -> { l: mkVestaPt p.l, r: mkVestaPt p.r })
      (pallasProofOpeningLrVec input.stepProof)

    z1Step :: StepField
    z1Step = pallasProofOpeningZ1 input.stepProof

    z2Step :: StepField
    z2Step = pallasProofOpeningZ2 input.stepProof

    deltaPt :: AffinePoint WrapField
    deltaPt = pallasProofOpeningDelta input.stepProof

    sgPt :: AffinePoint WrapField
    sgPt = pallasProofOpeningSg input.stepProof

    openingOut
      :: WrapProofOpening
           StepIPARounds
           (WeierstrassAffinePoint VestaG (F WrapField))
           (Type1 (F WrapField))
    openingOut = WrapProofOpening
      { lr: lrVec
      , z1: toShifted (F z1Step :: F StepField)
      , z2: toShifted (F z2Step :: F StepField)
      , delta: mkVestaPt deltaPt
      , sg: mkVestaPt sgPt
      }

    -- ===== Req.Proof_state. =====
    wrapProofStateOut
      :: WrapPrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
    wrapProofStateOut = WrapPrevProofState
      { unfinalizedProofs: input.prevUnfinalizedProofs
      , messagesForNextStepProof: input.prevMessagesForNextStepProofHash
      }
  in
    { whichBranch: input.whichBranch
    , wrapProofState: wrapProofStateOut
    , stepAccs: input.prevStepAccs
    , oldBpChals: input.prevOldBpChals
    , evals: input.prevEvals
    , wrapDomainIndices: input.prevWrapDomainIndices
    , openingProof: openingOut
    , messages: messagesOut
    }

--------------------------------------------------------------------------------
-- wrapProve — compile + solve + kimchi proof creation.
--
-- Analog of OCaml `Wrap.wrap` (top-level entry point at `wrap.ml:279`).
-- Mirrors the structure of the test harness's `createTestContext'`
-- but bound to `wrapMain`, serving advice through `WrapProverT`, and
-- using the production endo choice (`endoScalar @f' @f`) rather than
-- the constraint-only `endoBase @f @f'` path used in tests.
--
-- The whole path threads through `WrapProverT branches MaxProofsVerified
-- slot0Width slot1Width m` for any `Monad m`. `compile`, `makeSolver`,
-- and `runSolverT` are all monad-polymorphic; the only thing the
-- monad needs to satisfy is `WrapWitnessM branches MaxProofsVerified
-- slot0Width slot1Width VestaG WrapField`, which our `WrapProverT`
-- instance provides for any base monad.
--
-- On a solver failure (`EvaluationError`) we throw an `Error` so the
-- driver's caller gets a standard exception instead of having to
-- pattern-match on a sum type.
--------------------------------------------------------------------------------

-- | Ambient data the wrap prover needs alongside the advice record.
-- |
-- | * `wrapMainConfig` — the step-side VKs, lagrange bases,
-- |   all-possible-domains, etc. that `wrapMain` takes as a
-- |   compile-time parameter.
-- | * `crs` — the wrap circuit's Pallas SRS.
-- | * `publicInput` — the packed wrap statement (from
-- |   `assembleWrapMainInput`). Drives both the compile-time shape
-- |   check (via `CircuitType`) and the solver input.
-- | * `advice` — the `WrapAdvice` record from `buildWrapAdvice`.
type WrapProveContext (branches :: Int) (mpv :: Int) (slots :: Type -> Type) =
  { wrapMainConfig :: WrapMainConfig branches
  , crs :: CRS PallasG
  , publicInput ::
      WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
  , advice :: WrapAdvice mpv slots
  -- | When `true`, enables prover-state debug checks, runs
  -- | `verifyProverIndex` against the solved witness, and dumps
  -- | `/tmp/ps_wrap_row_labels.txt` for debugging witness
  -- | mismatches. Off by default — these checks are redundant once
  -- | the wrap prover is known to be correct.
  , debug :: Boolean
  -- | Kimchi-level `prev_challenges` for `ProverProof::create_recursive`.
  -- | Padded to `PaddedLength = 2` entries (via `Wrap_hack.pad_accumulator`).
  -- | Each entry holds sg (Pallas point, StepField coords) + expanded
  -- | challenges (WrapIPARounds = 15, in WrapField). Converted to Array
  -- | at the FFI boundary.
  , kimchiPrevChallenges ::
      Vector PaddedLength
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  }

-- | Ambient data `wrapCompile` needs — a subset of `WrapProveContext`
-- | without the solver-only fields (`publicInput`, `advice`).
type WrapCompileContext (branches :: Int) =
  { wrapMainConfig :: WrapMainConfig branches
  , crs :: CRS PallasG
  }

-- | Artifacts produced by `wrapCompile`. The prover / verifier index
-- | are created here so callers that split compile from solve can
-- | feed the `verifierIndex` into downstream logic (e.g. the step
-- | prover's `buildStepAdviceWithOracles`) before the solver runs.
type WrapCompileResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , constraintSystem :: ConstraintSystem WrapField
  , builtState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
  , constraints :: Array (KimchiRow WrapField)
  }

-- | Artifacts produced by `wrapProve`.
-- |
-- | Mirrors `TestContext'` shape so downstream code that previously
-- | consumed a `WrapProofContext` can be retargeted with minimal
-- | glue.
type WrapProveResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , constraintSystem :: ConstraintSystem WrapField
  , witness :: Vector 15 (Array WrapField)
  , publicInputs :: Array WrapField
  , proof :: Proof PallasG WrapField
  , assignments :: Map Variable WrapField
  }

-- | Compile phase of the wrap prover. Walks `wrapMain`'s circuit
-- | shape in `Effect`, which dispatches to the `WrapWitnessM Effect`
-- | instance — every advice method there throws. The advice values
-- | are never inspected during compile, so no caller placeholder is
-- | needed; anything that escapes the throw instance is a bug.
wrapCompile
  :: forall @branches @slots mpv branchesPred totalBases totalBasesPred
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  => Add mpv 45 totalBases
  => Add 1 totalBasesPred totalBases
  => PadSlots slots mpv
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => WrapCompileContext branches
  -> Effect WrapCompileResult
wrapCompile ctx = do
  builtState <-
    compile
      (Proxy @(WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint WrapField))
      (wrapMain @branches @slots ctx.wrapMainConfig)
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystemWithPrevChallenges @WrapField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @PaddedLength)
      }

    -- The wrap prover index's `cs.endo` field must be the WRAP curve's
    -- endo_base (= Vesta.endo_base = Wrap_inner_curve.base), NOT the
    -- endo_scalar that earlier (untested) commits had set. Trace evidence
    -- (`KIMCHI_STUBS_DEBUG: index.endo`) at the dummy-wrap-proof oracle
    -- call confirms OCaml uses `Vesta.endo_base()` here. See
    -- `memory/project_simple_chain_max_poly_size_bug.md` and the parallel
    -- step-side fix in `Pickles.Prove.Step.purs:1429-1431` (commit
    -- `20674463`) — same root cause, opposite curve.
    endo :: WrapField
    endo =
      let EndoBase e = (endoBase :: EndoBase WrapField) in e

    proverIndex =
      createProverIndex @WrapField @PallasG
        { endo, constraintSystem, crs: ctx.crs }

    verifierIndex = createVerifierIndex @WrapField @PallasG proverIndex

  pure
    { proverIndex
    , verifierIndex
    , constraintSystem
    , builtState
    , constraints
    }

-- | Solve phase of the wrap prover. Takes a previously compiled
-- | `WrapCompileResult` + the real advice + public input, runs the
-- | solver, and creates the kimchi proof. Errors surface through
-- | `ExceptT EvaluationError m` — the same error type the underlying
-- | `SolverT` uses. Constraint-system-unsatisfied failures are
-- | reported as `FailedAssertion`.
wrapSolveAndProve
  :: forall @branches @slots mpv branchesPred totalBases totalBasesPred m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  => Add mpv 45 totalBases
  => Add 1 totalBasesPred totalBases
  => PadSlots slots mpv
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => Monad m
  => WrapProveContext branches mpv slots
  -> WrapCompileResult
  -> ExceptT EvaluationError m WrapProveResult
wrapSolveAndProve ctx compileResult = do
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           (WrapProverT branches mpv slots m)
           (WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver' (emptyProverState { debug = ctx.debug }) (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slots ctx.wrapMainConfig)

  eRes <- lift $ runWrapProverT ctx.advice (runSolverT rawSolver ctx.publicInput)

  case eRes of
    Left e -> throwError (WithContext "wrapProve solver" e)
    Right (Tuple _ assignments) -> do
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }
      when ctx.debug do
        let _ = unsafePerformEffect (wrapDumpRowLabels compileResult.builtState.constraints)
        let
          csSatisfied = verifyProverIndex @WrapField @PallasG
            { proverIndex: compileResult.proverIndex, witness, publicInputs }
        when (not csSatisfied) $
          throwError (FailedAssertion "wrapProve: constraint system not satisfied (wrote row→label map to /tmp/ps_wrap_row_labels.txt)")
      let
        proof = vestaCreateProofWithPrev
          { proverIndex: compileResult.proverIndex
          , witness
          , prevChallenges:
              map
                ( \r ->
                    { sgX: r.sgX
                    , sgY: r.sgY
                    , challenges: Vector.toUnfoldable r.challenges
                    }
                )
                (Vector.toUnfoldable ctx.kimchiPrevChallenges :: Array _)
          }
      pure
        { proverIndex: compileResult.proverIndex
        , verifierIndex: compileResult.verifierIndex
        , constraintSystem: compileResult.constraintSystem
        , witness
        , publicInputs
        , proof
        , assignments
        }

-- | Debug helper: dump row → label mapping for the wrap circuit,
-- | so a `/tmp/ps_wrap_row_labels.txt` file can cross-reference a
-- | failing row in the kimchi witness diff against the labelled
-- | constraint source. Only fires when `WrapProveContext.debug`.
wrapDumpRowLabels :: Array (Labeled (KimchiGate WrapField)) -> Effect Unit
wrapDumpRowLabels constraints =
  let
    { out } = Array.foldl
      ( \{ row, out } lc ->
          let
            nRows = Array.length (toKimchiRows lc.constraint :: Array (KimchiRow WrapField))
            endRow = row + nRows - 1
            path = Array.intercalate "/" lc.context
            line = show row <> ".." <> show endRow <> "\t" <> path
          in
            { row: row + nRows, out: out <> [ line ] }
      )
      { row: 0, out: [] }
      constraints
  in
    FS.writeTextFile UTF8 "/tmp/ps_wrap_row_labels.txt"
      (Array.intercalate "\n" out <> "\n")

extractStepVKComms
  :: VerifierIndex VestaG StepField
  -> StepVK WrapField
extractStepVKComms vk =
  let
    comms = pallasVerifierIndexCommitments vk
  in
    { sigmaComm: comms.sigma
    , coefficientsComm: comms.coeff
    , genericComm: Vector.index comms.index (unsafeFinite @6 0)
    , psmComm: Vector.index comms.index (unsafeFinite @6 1)
    , completeAddComm: Vector.index comms.index (unsafeFinite @6 2)
    , mulComm: Vector.index comms.index (unsafeFinite @6 3)
    , emulComm: Vector.index comms.index (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index comms.index (unsafeFinite @6 5)
    }

-- | Lift a constant `StepVK WrapField` into a `StepVK (FVar WrapField)`
-- | by `const_`-ing each coordinate. Used by `buildWrapMainConfigN1`
-- | because `wrapMain`'s config carries step-key commitments as circuit
-- | variables so the in-circuit `chooseKey` can scale them by a boolean.
stepVkForCircuit :: StepVK WrapField -> StepVK (FVar WrapField)
stepVkForCircuit vk =
  let
    cp :: AffinePoint WrapField -> AffinePoint (FVar WrapField)
    cp pt = { x: const_ pt.x, y: const_ pt.y }
  in
    { sigmaComm: map cp vk.sigmaComm
    , coefficientsComm: map cp vk.coefficientsComm
    , genericComm: cp vk.genericComm
    , psmComm: cp vk.psmComm
    , completeAddComm: cp vk.completeAddComm
    , mulComm: cp vk.mulComm
    , emulComm: cp vk.emulComm
    , endomulScalarComm: cp vk.endomulScalarComm
    }

-- | Build a `WrapMainConfig 1` for a single-branch Simple_chain-style
-- | compile. Takes the compiled step verifier index, the Vesta
-- | (step-side) SRS used for the lagrange base lookup, and the step
-- | circuit's own domain log2 (= 16 for Simple_chain per
-- | `dump_circuit_impl.ml:3721-3723`).
-- |
-- | The lagrange closure calls `pallasSrsLagrangeCommitmentAt` on
-- | demand — kimchi caches the full basis after the first call, so
-- | per-index access is amortized O(1). The blinding `H` point comes
-- | from the same Vesta SRS. `allPossibleDomainLog2s` is hardcoded to
-- | `{13, 14, 15}` matching OCaml's `Wrap_verifier.all_possible_domains`
-- | for `proofs_verified ∈ {0,1,2}`.
-- | Single-branch wrap main config. The wrap circuit always verifies
-- | exactly ONE step proof regardless of that step's `max_proofs_verified`
-- | — what differs between N=0 / N=1 / N=2 rules is:
-- |
-- |   * `stepWidth` — the step rule's `max_proofs_verified` (OCaml's
-- |     `Widths`; 0 for No_recursion_return, 1 for Simple_chain,
-- |     2 for Simple_chain_n2 / Tree_proof_return).
-- |   * `domainLog2` — the step circuit's kimchi domain log2, read
-- |     dynamically from the compiled step prover index.
-- |
-- | All other fields (lagrange lookup, blinding H, the three possible
-- | wrap-domains) are structural constants of the Tock SRS, independent
-- | of N.
buildWrapMainConfig
  :: CRS VestaG
  -> VerifierIndex VestaG StepField
  -> { stepWidth :: Int, domainLog2 :: Int }
  -> WrapMainConfig 1
buildWrapMainConfig vestaSrs stepVK { stepWidth, domainLog2 } =
  { stepWidths: stepWidth :< Vector.nil
  , domainLog2s: domainLog2 :< Vector.nil
  , stepKeys: stepVkForCircuit (extractStepVKComms stepVK) :< Vector.nil
  , lagrangeAt:
      mkConstLagrangeBaseLookup \i ->
        (coerce (pallasSrsLagrangeCommitmentAt vestaSrs domainLog2 i))
          :: AffinePoint (F WrapField)
  , blindingH: (coerce $ pallasSrsBlindingGenerator vestaSrs) :: AffinePoint (F WrapField)
  , allPossibleDomainLog2s:
      unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
  }

