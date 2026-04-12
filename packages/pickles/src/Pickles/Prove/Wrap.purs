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
  , WrapProveResult
  , wrapProve
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception (Error, error)
import Partial.Unsafe (unsafePartial)
import Pickles.ProofFFI (Proof, createProof, pallasProofCommitments, pallasProofOpeningDelta, pallasProofOpeningLr, pallasProofOpeningSg, pallasProofOpeningZ1, pallasProofOpeningZ2)
import Pickles.Types (PaddedLength, PerProofUnfinalized, StepAllEvals, StepField, StepIPARounds, WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Slots (class PadSlots, Slots2)
import Prim.Int (class Add)
import Snarky.Backend.Compile (SolverT, compile, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.Kimchi (Type1, Type2, toShifted)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
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
type WrapProveContext (branches :: Int) (slot0Width :: Int) (slot1Width :: Int) =
  { wrapMainConfig :: WrapMainConfig branches
  , crs :: CRS PallasG
  , publicInput ::
      WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
  , advice :: WrapAdvice 2 (Slots2 slot0Width slot1Width)
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
wrapProve
  :: forall branches slot0Width slot1Width pad0 pad1 branchesPred m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Reflectable pad0 Int
  => Reflectable pad1 Int
  => Add pad0 slot0Width PaddedLength
  => Add pad1 slot1Width PaddedLength
  => Add 1 branchesPred branches
  => Monad m
  => (Error -> m WrapProveResult)
  -> WrapProveContext branches slot0Width slot1Width
  -> m WrapProveResult
wrapProve onError ctx = do
  -- ===== compile =====
  -- `compile` is monad-polymorphic; we run it in the same
  -- `WrapProverT` stack the solver uses so instance resolution lines
  -- up. The advice methods are never actually invoked here — compile
  -- walks the circuit shape without evaluating `exists` aux bodies.
  --
  -- The explicit annotation on the `compile` result pins
  -- `WrapProverT`'s phantom parameters, which is what lets
  -- instance resolution find our `WrapWitnessM` instance.
  let
    compileAction
      :: WrapProverT branches 2 (Slots2 slot0Width slot1Width) m
           (CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))
    compileAction =
      compile
        (Proxy @(WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slot0Width @slot1Width ctx.wrapMainConfig)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))

  builtState <- runWrapProverT ctx.advice compileAction

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystem @WrapField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      }

  -- ===== solve (populates assignments via advice methods) =====
  -- Pin the solver's monad with an explicit type signature: the same
  -- `WrapProverT` stack we used for compile, so the compiler can
  -- discharge the `WrapWitnessM` constraint via our instance.
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           (WrapProverT branches 2 (Slots2 slot0Width slot1Width) m)
           (WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slot0Width @slot1Width ctx.wrapMainConfig)

  eRes <- runWrapProverT ctx.advice (runSolverT rawSolver ctx.publicInput)

  case eRes of
    Left e -> onError (error ("wrapProve solver: " <> show e))
    Right (Tuple _ assignments) ->
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: builtState.publicInputs
          }

        -- Production endo choice: `endoScalar @f' @f`. For wrap
        -- circuit f = WrapField, f' = StepField — the memory note
        -- on endo coefficients spells out why `endoBase` works for
        -- constraint satisfaction only but `endoScalar` is required
        -- for verifiable proofs.
        endo :: WrapField
        endo =
          let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

        proverIndex =
          createProverIndex @WrapField @PallasG
            { endo, constraintSystem, crs: ctx.crs }

        verifierIndex = createVerifierIndex @WrapField @PallasG proverIndex
        proof = createProof { proverIndex, witness }
      in
        pure
          { proverIndex
          , verifierIndex
          , constraintSystem
          , witness
          , publicInputs
          , proof
          , assignments
          }
