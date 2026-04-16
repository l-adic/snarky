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
  , wrapProve
  , extractStepVKComms
  , stepVkForCircuit
  , buildWrapMainConfigN1
  , zeroWrapAdvice
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Exception (Error, error)
import Partial.Unsafe (unsafePartial)
import Pickles.ProofFFI (Proof, pallasProofCommitments, pallasProofOpeningDelta, pallasProofOpeningLr, pallasProofOpeningSg, pallasProofOpeningZ1, pallasProofOpeningZ2, pallasSigmaCommLast, pallasSrsBlindingGenerator, pallasSrsLagrangeCommitmentAt, pallasVerifierIndexColumnComms, vestaCreateProofWithPrev)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked)
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Slots (class PadSlots, replicateSlots)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, F(..), FVar, UnChecked(..), const_)
import Snarky.Circuit.Types (class CircuitType)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), toShifted)
import Snarky.Backend.Builder (CircuitBuilderState)
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

    tCommVec :: Vector 7 (WeierstrassAffinePoint VestaG (F WrapField))
    tCommVec = unsafePartial $ fromJust $
      Vector.toVector @7 (map mkVestaPt commits.tComm)

    messagesOut :: WrapProofMessages (WeierstrassAffinePoint VestaG (F WrapField))
    messagesOut = WrapProofMessages
      { wComm: map mkVestaPt commits.wComm
      , zComm: mkVestaPt commits.zComm
      , tComm: tCommVec
      }

    -- ===== Req.Openings_proof. =====
    --
    -- Step proof's bulletproof opening: lr pairs (length StepIPARounds),
    -- delta / sg curve points, and z1/z2 scalars. The scalars are
    -- `StepField` values; cross-field `toShifted` packs them as
    -- `Type1 (F WrapField)` via the `Shifted (F StepField)
    -- (Type1 (F WrapField))` instance.
    lrRaw :: Array { l :: AffinePoint WrapField, r :: AffinePoint WrapField }
    lrRaw = pallasProofOpeningLr input.stepProof

    lrVec
      :: Vector StepIPARounds
           { l :: WeierstrassAffinePoint VestaG (F WrapField)
           , r :: WeierstrassAffinePoint VestaG (F WrapField)
           }
    lrVec = unsafePartial $ fromJust $
      Vector.toVector @StepIPARounds
        (map (\p -> { l: mkVestaPt p.l, r: mkVestaPt p.r }) lrRaw)

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

-- | Run the wrap prover end-to-end. The monad `m` is constrained
-- | only by what `compile` / `runSolverT` need + what `throwError`
-- | needs to surface solver failures: `MonadThrow Error m`.
-- | Compile phase of the wrap prover. Walks `wrapMain`'s circuit
-- | shape under `WrapProverT`, produces the constraint system +
-- | prover/verifier index. The `advice` argument is threaded to
-- | `runWrapProverT` for instance resolution but its values are
-- | never inspected during compile — callers can pass a placeholder.
wrapCompile
  :: forall @branches @slots mpv branchesPred mpvPred totalBases totalBasesPred m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Add 1 mpvPred mpv
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
  => WrapCompileContext branches
  -> WrapAdvice mpv slots
  -> m WrapCompileResult
wrapCompile ctx advice = do
  let
    compileAction
      :: WrapProverT branches mpv slots m
           (CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))
    compileAction =
      compile
        (Proxy @(WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slots ctx.wrapMainConfig)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))

  builtState <- runWrapProverT advice compileAction

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
-- | solver, and creates the kimchi proof.
wrapSolveAndProve
  :: forall @branches @slots mpv branchesPred mpvPred totalBases totalBasesPred m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Add 1 mpvPred mpv
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
  => (Error -> m WrapProveResult)
  -> WrapProveContext branches mpv slots
  -> WrapCompileResult
  -> m WrapProveResult
wrapSolveAndProve onError ctx compileResult = do
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           (WrapProverT branches mpv slots m)
           (WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver' (emptyProverState { debug = true }) (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slots ctx.wrapMainConfig)

  eRes <- runWrapProverT ctx.advice (runSolverT rawSolver ctx.publicInput)

  case eRes of
    Left e -> onError (error ("wrapProve solver: " <> show e))
    Right (Tuple _ assignments) ->
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }

        csSatisfied = verifyProverIndex @WrapField @PallasG
          { proverIndex: compileResult.proverIndex, witness, publicInputs }
      in
        if not csSatisfied then
          onError (error "wrapProve: constraint system not satisfied")
        else
          let proof = vestaCreateProofWithPrev
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
          in pure
            { proverIndex: compileResult.proverIndex
            , verifierIndex: compileResult.verifierIndex
            , constraintSystem: compileResult.constraintSystem
            , witness
            , publicInputs
            , proof
            , assignments
            }

-- | End-to-end wrap prover: `wrapCompile` then `wrapSolveAndProve`.
wrapProve
  :: forall @branches @slots mpv branchesPred mpvPred totalBases totalBasesPred m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Add 1 mpvPred mpv
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
  => (Error -> m WrapProveResult)
  -> WrapProveContext branches mpv slots
  -> m WrapProveResult
wrapProve onError ctx = do
  compileResult <- wrapCompile @branches @slots
    { wrapMainConfig: ctx.wrapMainConfig, crs: ctx.crs }
    ctx.advice
  wrapSolveAndProve @branches @slots onError ctx compileResult

--------------------------------------------------------------------------------
-- Wrap VK extraction helpers for Simple_chain driver
--
-- These helpers let the Simple_chain test (and anything else with the
-- same shape) build a `WrapMainConfig 1` from a compiled step
-- `VerifierIndex` + a Vesta SRS, without hand-wiring all the
-- lagrange-base / blinding / domain plumbing. They also expose a
-- baseline `zeroWrapAdvice` for `wrapCompile`'s advice slot (compile
-- doesn't inspect values, just the type shape).
--
-- References:
--   `git show 1f9611e3:packages/pickles/test/Test/Pickles/Prove/WrapE2E.purs`
--     lines 56-113 (old `extractStepVKComms` / `stepVkForCircuit` /
--     `buildWrapMainConfig` helpers, ported here with updated lagrange
--     lookup shape).
--   `packages/pickles/src/Pickles/Wrap/Main.purs:104-111`
--     (current `WrapMainConfig` record shape).
--------------------------------------------------------------------------------

-- | Extract the step-side (Vesta curve) VK commitments from a compiled
-- | step verifier index, in the `StepVK WrapField` shape `wrapMain`
-- | embeds in its config (as circuit variables via `stepVkForCircuit`).
-- |
-- | The 27 column commitments are returned in `to_batch` order by the
-- | FFI: `index (6) + coefficient (15) + sigma (6)`. The 7th sigma
-- | comes from a separate FFI call. Pallas column comms are Vesta
-- | points with coordinates in `Vesta.BaseField = WrapField`.
extractStepVKComms
  :: VerifierIndex VestaG StepField
  -> StepVK WrapField
extractStepVKComms vk =
  let
    raw :: Array (AffinePoint WrapField)
    raw = pallasVerifierIndexColumnComms vk

    idx6 :: Vector 6 (AffinePoint WrapField)
    idx6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.take 6 raw

    coeff15 :: Vector 15 (AffinePoint WrapField)
    coeff15 = unsafePartial $ fromJust $ Vector.toVector @15 $
      Array.take 15 $ Array.drop 6 raw

    sig6 :: Vector 6 (AffinePoint WrapField)
    sig6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.drop 21 raw

    sigLast :: AffinePoint WrapField
    sigLast = pallasSigmaCommLast vk
  in
    { sigmaComm: Vector.snoc sig6 sigLast
    , coefficientsComm: coeff15
    , genericComm: Vector.index idx6 (unsafeFinite @6 0)
    , psmComm: Vector.index idx6 (unsafeFinite @6 1)
    , completeAddComm: Vector.index idx6 (unsafeFinite @6 2)
    , mulComm: Vector.index idx6 (unsafeFinite @6 3)
    , emulComm: Vector.index idx6 (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index idx6 (unsafeFinite @6 5)
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
buildWrapMainConfigN1
  :: CRS VestaG
  -> VerifierIndex VestaG StepField
  -> Int
  -> WrapMainConfig 1
buildWrapMainConfigN1 vestaSrs stepVK domainLog2 =
  { stepWidths: 1 :< Vector.nil
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

-- | Baseline zero-valued `WrapAdvice mpv slots` for the compile phase.
-- | `wrapCompile` threads the advice to `runWrapProverT` only for
-- | type-class instance resolution; the values are never read during
-- | circuit shape walking. Callers hand this in to `wrapCompile` when
-- | they don't yet have real advice (e.g. when they need the compiled
-- | wrap VK BEFORE the step solver runs so they can feed it to
-- | `buildStepAdviceWithOracles`).
-- |
-- | Polymorphic in the slot shape via `PadSlots.replicateSlots`, which
-- | builds a `slots`-shaped value of zero bp-challenge stacks.
zeroWrapAdvice
  :: forall mpv slots
   . Reflectable mpv Int
  => PadSlots slots mpv
  => WrapAdvice mpv slots
zeroWrapAdvice =
  let
    zeroF :: F WrapField
    zeroF = F zero

    zeroType1 :: Type1 (F WrapField)
    zeroType1 = Type1 zeroF

    zeroType2 :: Type2 (F WrapField)
    zeroType2 = Type2 zeroF

    zeroUncheckedSized128 :: UnChecked (SizedF 128 (F WrapField))
    zeroUncheckedSized128 = UnChecked (unsafePartial (unsafeFromField zeroF))

    zeroWeierstrass :: WeierstrassAffinePoint VestaG (F WrapField)
    zeroWeierstrass = WeierstrassAffinePoint { x: zeroF, y: zeroF }

    zeroPointEval :: PointEval (F WrapField)
    zeroPointEval = PointEval { zeta: zeroF, omegaTimesZeta: zeroF }

    zeroStepAllEvals :: StepAllEvals (F WrapField)
    zeroStepAllEvals = StepAllEvals
      { publicEvals: zeroPointEval
      , witnessEvals: Vector.replicate zeroPointEval
      , coeffEvals: Vector.replicate zeroPointEval
      , zEvals: zeroPointEval
      , sigmaEvals: Vector.replicate zeroPointEval
      , indexEvals: Vector.replicate zeroPointEval
      , ftEval1: zeroF
      }

    zeroPerProof :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean
    zeroPerProof = PerProofUnfinalized
      { combinedInnerProduct: zeroType2
      , b: zeroType2
      , zetaToSrsLength: zeroType2
      , zetaToDomainSize: zeroType2
      , perm: zeroType2
      , spongeDigest: zeroF
      , beta: zeroUncheckedSized128
      , gamma: zeroUncheckedSized128
      , alpha: zeroUncheckedSized128
      , zeta: zeroUncheckedSized128
      , xi: zeroUncheckedSized128
      , bulletproofChallenges: Vector.replicate zeroUncheckedSized128
      , shouldFinalize: false
      }

    -- Polymorphic in the slot shape via `PadSlots.replicateSlots`,
    -- which broadcasts the seed `Vector WrapIPARounds (F WrapField)`
    -- (= a single bp-challenge stack of zeros) into the slots-shaped
    -- structure.
    zeroChalStack :: Vector WrapIPARounds (F WrapField)
    zeroChalStack = Vector.replicate zeroF

    zeroSlots :: slots (Vector WrapIPARounds (F WrapField))
    zeroSlots = replicateSlots zeroChalStack

    zeroOpening
      :: WrapProofOpening
           StepIPARounds
           (WeierstrassAffinePoint VestaG (F WrapField))
           (Type1 (F WrapField))
    zeroOpening = WrapProofOpening
      { lr: Vector.replicate { l: zeroWeierstrass, r: zeroWeierstrass }
      , z1: zeroType1
      , z2: zeroType1
      , delta: zeroWeierstrass
      , sg: zeroWeierstrass
      }

    zeroMessages :: WrapProofMessages (WeierstrassAffinePoint VestaG (F WrapField))
    zeroMessages = WrapProofMessages
      { wComm: Vector.replicate zeroWeierstrass
      , zComm: zeroWeierstrass
      , tComm: Vector.replicate zeroWeierstrass
      }
  in
    { whichBranch: zeroF
    , wrapProofState: WrapPrevProofState
        { unfinalizedProofs: Vector.replicate zeroPerProof
        , messagesForNextStepProof: zeroF
        }
    , stepAccs: Vector.replicate zeroWeierstrass
    , oldBpChals: zeroSlots
    , evals: Vector.replicate zeroStepAllEvals
    , wrapDomainIndices: Vector.replicate zeroF
    , openingProof: zeroOpening
    , messages: zeroMessages
    }
