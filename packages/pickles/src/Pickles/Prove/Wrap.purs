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
  , buildWrapMainConfigMulti
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
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.Process as Process
import Pickles.Field (StepField, WrapField)
import Pickles.ProofFFI (Proof, pallasProofCommitments, pallasProofOpeningDelta, pallasProofOpeningLrVec, pallasProofOpeningSg, pallasProofOpeningZ1, pallasProofOpeningZ2, pallasSrsBlindingGenerator, pallasSrsLagrangeCommitmentAt, pallasVerifierIndexCommitments, tCommChunked, vestaCreateProofWithPrev, wCommChunked, zCommChunked)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Types (PaddedLength, PerProofUnfinalized, StepAllEvals, StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Slots (class PadSlots)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, crsSize, verifyProverIndex)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasConstraintSystemToJson)
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
type WrapAdvice (mpv :: Int) (numChunks :: Int) (slots :: Type -> Type) =
  { whichBranch :: F WrapField
  , wrapProofState ::
      Wrap.PrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
  , stepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  , oldBpChals :: slots (Vector WrapIPARounds (F WrapField))
  , evals :: Vector mpv (StepAllEvals (F WrapField))
  , wrapDomainIndices :: Vector mpv (F WrapField)
  , openingProof ::
      WrapProofOpening
        StepIPARounds
        (WeierstrassAffinePoint VestaG (F WrapField))
        (Type1 (F WrapField))
  -- | `numChunks` here is THIS compile's own num_chunks — the wrap is
  -- | wrapping a step proof from the current compile, whose commitments
  -- | are at the current compile's chunk count.
  , messages :: WrapProofMessages numChunks (WeierstrassAffinePoint VestaG (F WrapField))
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
  -> Int
  -> (Type -> Type)
  -> (Type -> Type)
  -> Type
  -> Type
newtype WrapProverT
  branches
  mpv
  numChunks
  slots
  m
  a = WrapProverT (ReaderT (WrapAdvice mpv numChunks slots) m a)

derive instance Newtype (WrapProverT branches mpv numChunks slots m a) _
derive newtype instance Functor m => Functor (WrapProverT branches mpv numChunks slots m)
derive newtype instance Apply m => Apply (WrapProverT branches mpv numChunks slots m)
derive newtype instance Applicative m => Applicative (WrapProverT branches mpv numChunks slots m)
derive newtype instance Bind m => Bind (WrapProverT branches mpv numChunks slots m)
derive newtype instance Monad m => Monad (WrapProverT branches mpv numChunks slots m)

-- | Supply the advice record and run the prover computation in the
-- | base monad.
runWrapProverT
  :: forall branches mpv numChunks slots m a
   . WrapAdvice mpv numChunks slots
  -> WrapProverT branches mpv numChunks slots m a
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
    numChunks
    slots
    VestaG
    WrapField
    (WrapProverT branches mpv numChunks slots m) where
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
--   step proof's own committed `Types.Statement` contents.
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
  :: forall @numChunks mpv slots
   . Reflectable numChunks Int
  => BuildWrapAdviceInput mpv slots
  -> WrapAdvice mpv numChunks slots
buildWrapAdvice input =
  let
    -- ===== Req.Messages (step.ml commitments → wrap witness). =====
    --
    -- `pallasProofCommitments` returns chunked w/z (Array per polynomial)
    -- and flat tComm. Project into typed Vector numChunks via
    -- wCommChunked/zCommChunked. tComm is still pinned to Vector 7 here
    -- (FFI does not yet emit chunked t).
    commits = pallasProofCommitments input.stepProof

    messages = WrapProofMessages
      { wComm: map (map mkVestaPt) (wCommChunked @numChunks commits)
      , zComm: map mkVestaPt (zCommChunked @numChunks commits)
      , tComm: map (map mkVestaPt) (tCommChunked @numChunks commits)
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

    z1Step = pallasProofOpeningZ1 input.stepProof

    z2Step = pallasProofOpeningZ2 input.stepProof

    deltaPt = pallasProofOpeningDelta input.stepProof

    sgPt = pallasProofOpeningSg input.stepProof

    openingProof
      :: WrapProofOpening
           StepIPARounds
           (WeierstrassAffinePoint VestaG (F WrapField))
           (Type1 (F WrapField))
    openingProof = WrapProofOpening
      { lr: lrVec
      , z1: toShifted (F z1Step)
      , z2: toShifted (F z2Step)
      , delta: mkVestaPt deltaPt
      , sg: mkVestaPt sgPt
      }

    -- ===== Req.Proof_state. =====
    wrapProofState
      :: Wrap.PrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
    wrapProofState = Wrap.PrevProofState
      { unfinalizedProofs: input.prevUnfinalizedProofs
      , messagesForNextStepProof: input.prevMessagesForNextStepProofHash
      }
  in
    { whichBranch: input.whichBranch
    , wrapProofState
    , stepAccs: input.prevStepAccs
    , oldBpChals: input.prevOldBpChals
    , evals: input.prevEvals
    , wrapDomainIndices: input.prevWrapDomainIndices
    , openingProof
    , messages
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
type WrapProveContext (branches :: Int) (mpv :: Int) (numChunks :: Int) (slots :: Type -> Type) =
  { wrapMainConfig :: WrapMainConfig branches numChunks
  , crs :: CRS PallasG
  , publicInput ::
      Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
  , advice :: WrapAdvice mpv numChunks slots
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
  { wrapMainConfig :: WrapMainConfig branches numChunks
  , crs :: CRS PallasG
  }

-- | Artifacts produced by `wrapCompile`. The prover / verifier index
-- | are created here so callers that split compile from solve can
-- | feed the `verifierIndex` into downstream logic (e.g. the step
-- | prover's `buildSlotAdvice`) before the solver runs.
type WrapCompileResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , constraintSystem :: ConstraintSystem WrapField
  , builtState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
  , constraints :: Array (KimchiRow WrapField)
  }

-- | Artifacts produced by `wrapProve`.
type WrapProveResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , constraintSystem :: ConstraintSystem WrapField
  , witness :: Vector 15 (Array WrapField)
  , publicInputs :: Array WrapField
  , proof :: Proof PallasG WrapField
  , assignments :: Map Variable WrapField
  }

-- | Monotonic counter for `KIMCHI_WRAP_CS_DUMP`'s `%c` template. Each
-- | wrap-circuit compile (one per top-level rule in `compileMulti`)
-- | increments it, mirroring the AtomicUsize counter on the Rust side.
wrapCsCounter :: Ref.Ref Int
wrapCsCounter = unsafePerformEffect (Ref.new 0)

bumpWrapCsCounter :: Effect Int
bumpWrapCsCounter = do
  n <- Ref.read wrapCsCounter
  Ref.write (n + 1) wrapCsCounter
  pure n

-- | Compile phase of the wrap prover. Walks `wrapMain`'s circuit
-- | shape in `Effect`, which dispatches to the `WrapWitnessM Effect`
-- | instance — every advice method there throws. The advice values
-- | are never inspected during compile, so no caller placeholder is
-- | needed; anything that escapes the throw instance is a bug.
wrapCompile
  :: forall @branches @slots @numChunks mpv branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCommN chunkBases nonSgBases sg1 sg2 sg3 sg4
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Reflectable numChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 numChunks LT
  => Mul 7 numChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 numChunks wCommN
  => Mul 16 numChunks chunkBases
  => Add 29 chunkBases nonSgBases
  => Add 2 numChunks sg1
  => Add sg1 6 sg2
  => Add sg2 wCommN sg3
  => Add sg3 15 sg4
  => Add sg4 6 nonSgBases
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  => Add mpv nonSgBases totalBases
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
      (Proxy @(Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint WrapField))
      (wrapMain @branches @slots @numChunks ctx.wrapMainConfig)
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystemWithPrevChallenges @WrapField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @PaddedLength)
      , maxPolySize: crsSize ctx.crs
      }

    -- The wrap prover index's `cs.endo` field must be the WRAP curve's
    -- endo_base (= Vesta.endo_base = Wrap_inner_curve.base), NOT the
    -- endo_scalar that earlier (untested) commits had set. Trace evidence
    -- (`KIMCHI_STUBS_DEBUG: index.endo`) at the dummy-wrap-proof oracle
    -- call confirms OCaml uses `Vesta.endo_base()` here. See
    -- `memory/project_simple_chain_max_poly_size_bug.md` and the parallel
    -- step-side fix in `Pickles.Prove.Step.purs:1429-1431` (commit
    -- `20674463`) — same root cause, opposite curve.
    endo =
      let EndoBase e = (endoBase) in e

    proverIndex =
      createProverIndex @WrapField @PallasG
        { endo, constraintSystem, crs: ctx.crs }

    verifierIndex = createVerifierIndex @WrapField @PallasG proverIndex

  -- Optional dump of the wrap constraint system as JSON, gated on
  -- `KIMCHI_WRAP_CS_DUMP`. Mirrors OCaml's `PICKLES_WRAP_CS_DUMP` in
  -- `compile.ml`. Filename template uses `%c` (replaced with a
  -- monotonic counter) so multi-rule compileMulti writes one file per
  -- branch — same convention as `KIMCHI_WITNESS_DUMP`.
  Process.lookupEnv "KIMCHI_WRAP_CS_DUMP" >>= case _ of
    Nothing -> pure unit
    Just pathTmpl -> do
      counter <- bumpWrapCsCounter
      let path = String.replaceAll (Pattern "%c") (Replacement (show counter)) pathTmpl
      FS.writeTextFile UTF8 path (pallasConstraintSystemToJson constraintSystem)

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
  :: forall @branches @slots @numChunks mpv branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCommN chunkBases nonSgBases sg1 sg2 sg3 sg4 m
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Reflectable numChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 numChunks LT
  => Mul 7 numChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 numChunks wCommN
  => Mul 16 numChunks chunkBases
  => Add 29 chunkBases nonSgBases
  => Add 2 numChunks sg1
  => Add sg1 6 sg2
  => Add sg2 wCommN sg3
  => Add sg3 15 sg4
  => Add sg4 6 nonSgBases
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  => Add mpv nonSgBases totalBases
  => Add 1 totalBasesPred totalBases
  => PadSlots slots mpv
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => Monad m
  => WrapProveContext branches mpv numChunks slots
  -> WrapCompileResult
  -> ExceptT EvaluationError m WrapProveResult
wrapSolveAndProve ctx compileResult = do
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           (WrapProverT branches mpv numChunks slots m)
           (Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver' (emptyProverState { debug = ctx.debug }) (Proxy @(KimchiConstraint WrapField))
        (wrapMain @branches @slots @numChunks ctx.wrapMainConfig)

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
                (Vector.toUnfoldable ctx.kimchiPrevChallenges)
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

-- | Multi-branch wrap main config. Takes per-branch data
-- | (`Vector branches { mpv, stepDomainLog2, stepVK }`) and produces a
-- | `WrapMainConfig branches` that the wrap circuit's
-- | `Pseudo.choose whichBranch` machinery dispatches over at proof
-- | time.
-- |
-- | The single-branch `buildWrapMainConfig` is degenerate-case sugar
-- | for `buildWrapMainConfigMulti @1` with a one-element vector;
-- | both produce the same `WrapMainConfig` structurally.
-- |
-- | Branch-domain dispatch mirrors OCaml's `lagrange_with_correction`
-- | (wrap_verifier.ml:382-443):
-- |
-- |   * **All branches share the same step domain** (fast path,
-- |     wrap_verifier.ml:426-428): the lagrange basis at that single
-- |     domain works for every branch — populate `lagrangeAt` from
-- |     it and set `perBranchLagrangeAt = Nothing`.
-- |   * **Branch domains differ** (per-branch path,
-- |     wrap_verifier.ml:429-443): for each index `i`, fetch one
-- |     constant lagrange point per branch (each at its branch's
-- |     `stepDomainLog2`); the wrap circuit performs the 1-hot sum
-- |     against `whichBranch` in-circuit. Populate
-- |     `perBranchLagrangeAt` from this; `lagrangeAt` is unused but
-- |     populated from the head branch's domain to satisfy the type.
buildWrapMainConfigMulti
  :: forall @branches branchesPred
   . Reflectable branches Int
  => Add 1 branchesPred branches
  => CRS VestaG
  -> { perBranch ::
         Vector branches
           { mpv :: Int
           , stepDomainLog2 :: Int
           , stepVK :: VerifierIndex VestaG StepField
           }
     }
  -> WrapMainConfig branches numChunks
buildWrapMainConfigMulti vestaSrs { perBranch } =
  let
    domainLog2s = map _.stepDomainLog2 perBranch
    headDomainLog2 = (Vector.uncons perBranch).head.stepDomainLog2
    allEqual = Array.all (_ == headDomainLog2)
      (Vector.toUnfoldable domainLog2s)
    perBranchLookup i =
      map
        ( \b ->
            (coerce (pallasSrsLagrangeCommitmentAt vestaSrs b.stepDomainLog2 i))
              :: AffinePoint (F WrapField)
        )
        perBranch
  in
    { stepWidths: map _.mpv perBranch
    , domainLog2s
    , stepKeys:
        map (\b -> stepVkForCircuit (extractStepVKComms b.stepVK)) perBranch
    , lagrangeAt:
        mkConstLagrangeBaseLookup \i ->
          (coerce (pallasSrsLagrangeCommitmentAt vestaSrs headDomainLog2 i))
            :: AffinePoint (F WrapField)
    , perBranchLagrangeAt:
        if allEqual then Nothing else Just perBranchLookup
    , blindingH: (coerce $ pallasSrsBlindingGenerator vestaSrs) :: AffinePoint (F WrapField)
    , allPossibleDomainLog2s:
        unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
    }

