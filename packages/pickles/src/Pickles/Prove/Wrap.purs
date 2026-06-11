-- | Prover-side infrastructure for `Pickles.Wrap.Main.wrapMain`.
-- |
-- | While `Pickles.Prove.Pure.Wrap` covers the **pure** pieces of the
-- | wrap prover (deferred-values derivation + statement assembly), this
-- | module provides the **effectful** glue that feeds `wrapMain`'s
-- | `Req.*` advice during witness generation:
-- |
-- | * `WrapAdvice` (re-exported from `Pickles.Wrap.Advice`) — a record
-- |   holding all 8 advice pieces (one per OCaml `Req.*` request) with
-- |   concrete, already-computed values, passed by value into `wrapMain`.
module Pickles.Prove.Wrap
  ( module Pickles.Wrap.Advice
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
import Control.Monad.Trans.Class (lift)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Lazy as Lazy
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (over, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.Process as Process
import Pickles.Field (StepField, WrapField)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Types (ChunkedCommitment(..), PaddedLength, PerProofUnfinalized, StepAllEvals, StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK, pallasVerifierIndexCommitments)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Slots (class PadSlots)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Run (EFFECT, Run)
import Run as Run
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled, constraintsToArray)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, crsSize, gatesToJson)
import Snarky.Backend.Kimchi.Proof (Proof, pallasProofCommitments, pallasProofData, srsBlindingGenerator, srsLagrangeCommitmentChunksAt, vestaCreateProofWithPrev)
import Snarky.Backend.Kimchi.ProofCache (ProofCache, getVestaProof, setVestaProof)
import Snarky.Backend.Kimchi.Types (CRS, Gate, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.DSL (class CheckedType, F(..), FVar, const_)
import Snarky.Circuit.Kimchi (Type1, Type2, toShifted)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

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
mkVestaPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

-- | Build the wrap-circuit advice record from the step proof + its
-- | surrounding pickles context. Pure: all FFI calls go through
-- | deterministic `pallas*` helpers exposed as non-effectful in
-- | `Snarky.Backend.Kimchi.Proof`.
buildWrapAdvice
  :: forall @stepChunks mpv slots
   . Reflectable stepChunks Int
  => BuildWrapAdviceInput mpv slots
  -> WrapAdvice mpv stepChunks slots
buildWrapAdvice input =
  let
    -- ===== Req.Messages (step.ml commitments → wrap witness). =====
    --
    -- One eager decode of the step proof; downstream uses
    -- field-access on the structured record.
    stepProofData = pallasProofData @StepIPARounds input.stepProof

    -- `nc`-typed commitments, decoded + chunk-validated once at @stepChunks.
    commits = pallasProofCommitments @stepChunks input.stepProof

    messages = WrapProofMessages
      { wComm: map (over ChunkedCommitment (map mkVestaPt)) commits.wComm
      , zComm: over ChunkedCommitment (map mkVestaPt) commits.zComm
      , tComm: map (over ChunkedCommitment (map mkVestaPt)) commits.tComm
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
      stepProofData.opening.lr

    z1Step = stepProofData.opening.z1

    z2Step = stepProofData.opening.z2

    deltaPt = stepProofData.opening.delta

    sgPt = stepProofData.opening.sg

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
-- but bound to `wrapMain`, passing the `WrapAdvice` record by value,
-- and using the production endo choice (`endoScalar @f' @f`) rather
-- than the constraint-only `endoBase @f @f'` path used in tests.
--
-- The whole path runs `wrapMain` in the caller's bare monad `m`: there
-- is no bespoke prover transformer. `compile`, `makeSolver`, and
-- `runSolverT` are all monad-polymorphic; `wrapMain` reads each advice
-- piece by projecting the `WrapAdvice` value inside an `exists` body.
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
type WrapProveContext (branches :: Int) (mpv :: Int) (stepChunks :: Int) (slots :: Type -> Type) =
  { wrapMainConfig :: WrapMainConfig branches stepChunks
  , crs :: CRS PallasG
  , publicInput ::
      Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
  , advice :: WrapAdvice mpv stepChunks slots
  -- | When `true`, enables prover-state debug checks, runs
  -- | `verifyProverIndex` against the solved witness, and dumps
  -- | `/tmp/ps_wrap_row_labels.txt` for debugging witness
  -- | mismatches. Off by default — these checks are redundant once
  -- | the wrap prover is known to be correct.
  , debug :: Boolean
  -- | Optional disk proof-cache (test/dev). Threaded from
  -- | `CompileMultiConfig`. `Nothing` = no caching.
  , proofCache :: Maybe ProofCache
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
type WrapCompileContext :: Int -> Int -> Type
type WrapCompileContext branches stepChunks =
  { wrapMainConfig :: WrapMainConfig branches stepChunks
  , crs :: CRS PallasG
  }

-- | Artifacts produced by `wrapCompile`. The prover / verifier index
-- | are created here so callers that split compile from solve can
-- | feed the `verifierIndex` into downstream logic (e.g. the step
-- | prover's `buildSlotAdvice`) before the solver runs.
type WrapCompileResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , gates :: Array (Gate WrapField)
  , publicInputSize :: Int
  , builtState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
  , constraints :: Array (KimchiRow WrapField)
  }

-- | Artifacts produced by `wrapProve`.
type WrapProveResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
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
-- | shape in `Effect` with a dummy `WrapAdvice` value. Every advice
-- | read lives inside an `exists` body, which `compile` discards, so
-- | the advice record is never projected — the dummy value is never
-- | forced.
wrapCompile
  :: forall @branches @slots @stepChunks numChunksPred mpv branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add stepChunks 1 sg1
  => Add sg1 stepChunks sg2
  => Add sg2 indexSigmaN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 wCoeffN sg5
  => Add sg5 indexSigmaN nonSgBases
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
  => WrapCompileContext branches stepChunks
  -> Effect WrapCompileResult
wrapCompile ctx = do
  -- Run `wrapMain`'s circuit in the bare base monad (`Effect`) with a
  -- dummy advice value. At compile every advice read lives inside an
  -- `exists` body, which `compile` discards, so the advice record is
  -- never projected — the `unsafeCoerce unit` bottom below is never
  -- forced.
  let
    dummyAdvice :: WrapAdvice mpv stepChunks slots
    dummyAdvice = unsafeCoerce unit
  let
    builtState = Run.extract $
      compile
        (Proxy @(Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @branches @slots @stepChunks ctx.wrapMainConfig stmt dummyAdvice)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField))

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
    csResult = makeConstraintSystemWithPrevChallenges @WrapField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @PaddedLength)
      , maxPolySize: crsSize ctx.crs
      }
    { gates, publicInputSize, constraints } = csResult

    -- `cs.endo` is no longer threaded through the PS signature: the JS
    -- impl of `createProverIndex` fetches the wrap curve's endo_base
    -- (= Vesta.endo_base = Wrap_inner_curve.base) from the napi layer
    -- directly. See `memory/project_simple_chain_max_poly_size_bug.md`
    -- and the step-side fix at `Pickles.Prove.Step.purs` (commit
    -- `20674463`) for the historical rationale.
    proverIndex =
      createProverIndex @WrapField @PallasG
        { gates
        , publicInputSize
        , prevChallengesCount: csResult.prevChallengesCount
        , maxPolySize: csResult.maxPolySize
        , crs: ctx.crs
        }

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
      FS.writeTextFile UTF8 path (gatesToJson gates publicInputSize)

  pure
    { proverIndex
    , verifierIndex
    , gates
    , publicInputSize
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
  :: forall @branches @slots @stepChunks numChunksPred mpv branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 r
   . CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpv Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add stepChunks 1 sg1
  => Add sg1 stepChunks sg2
  => Add sg2 indexSigmaN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 wCoeffN sg5
  => Add sg5 indexSigmaN nonSgBases
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
  => WrapProveContext branches mpv stepChunks slots
  -> WrapCompileResult
  -> ExceptT EvaluationError (Run (EFFECT + r)) WrapProveResult
wrapSolveAndProve ctx compileResult = do
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           (EFFECT + r)
           (Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver' (emptyProverState { debug = ctx.debug }) (Proxy @(KimchiConstraint WrapField))
        (\stmt -> wrapMain @branches @slots @stepChunks ctx.wrapMainConfig stmt ctx.advice)

  eRes <- lift $ runSolverT rawSolver ctx.publicInput

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
        let _ = unsafePerformEffect (wrapDumpRowLabels (constraintsToArray compileResult.builtState.constraints))
        pure unit
      let
        p = Lazy.defer \_ -> vestaCreateProofWithPrev
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
      proof <-
        case ctx.proofCache of
          Nothing -> pure $ Lazy.force p
          Just cache -> do
            mp <- liftEffect $ getVestaProof cache compileResult.verifierIndex publicInputs
            case mp of
              Just proof -> pure proof
              Nothing -> do
                let proof = Lazy.force p
                liftEffect $ setVestaProof cache compileResult.verifierIndex publicInputs proof
                pure proof
      pure
        { proverIndex: compileResult.proverIndex
        , verifierIndex: compileResult.verifierIndex
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
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex VestaG StepField
  -> StepVK stepChunks WrapField
extractStepVKComms vk =
  let
    comms = pallasVerifierIndexCommitments @stepChunks vk
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
stepVkForCircuit
  :: forall stepChunks
   . StepVK stepChunks WrapField
  -> StepVK stepChunks (FVar WrapField)
stepVkForCircuit vk =
  let
    cp :: AffinePoint WrapField -> AffinePoint (FVar WrapField)
    cp (AffinePoint pt) = AffinePoint { x: const_ pt.x, y: const_ pt.y }
    cpChunk = over ChunkedCommitment (map cp)
  in
    { sigmaComm: map cpChunk vk.sigmaComm
    , coefficientsComm: map cpChunk vk.coefficientsComm
    , genericComm: cpChunk vk.genericComm
    , psmComm: cpChunk vk.psmComm
    , completeAddComm: cpChunk vk.completeAddComm
    , mulComm: cpChunk vk.mulComm
    , emulComm: cpChunk vk.emulComm
    , endomulScalarComm: cpChunk vk.endomulScalarComm
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
  :: forall @branches @stepChunks branchesPred
   . Reflectable branches Int
  => Reflectable stepChunks Int
  => Add 1 branchesPred branches
  => CRS VestaG
  -> { perBranch ::
         Vector branches
           { mpv :: Int
           , stepDomainLog2 :: Int
           , stepVK :: VerifierIndex VestaG StepField
           }
     }
  -> WrapMainConfig branches stepChunks
buildWrapMainConfigMulti vestaSrs { perBranch } =
  let
    domainLog2s = map _.stepDomainLog2 perBranch
    headDomainLog2 = (Vector.uncons perBranch).head.stepDomainLog2
    allEqual = Array.all (_ == headDomainLog2)
      (Vector.toUnfoldable domainLog2s)
    perBranchLookup i =
      map
        ( \b ->
            let
              chunksArr = srsLagrangeCommitmentChunksAt
                vestaSrs
                b.stepDomainLog2
                i
            in
              case Vector.toVector @stepChunks (map coerce chunksArr) of
                Just v -> (v :: Vector _ (AffinePoint (F WrapField)))
                Nothing -> unsafeThrow
                  $ "buildWrapMainConfigMulti.perBranchLookup: lagrange chunks size mismatch "
                      <> "(got "
                      <> show (Array.length chunksArr)
                      <> ", expected stepChunks="
                      <> show (reflectType (Proxy @stepChunks))
                      <> ")"
        )
        perBranch
  in
    { stepWidths: map _.mpv perBranch
    , domainLog2s
    , stepKeys:
        map (\b -> stepVkForCircuit (extractStepVKComms b.stepVK)) perBranch
    , lagrangeAt:
        -- Wrap-side lagrange: chunked at chunks2. For each PI slot the
        -- basis splits into `stepChunks = ceil(2^stepDomainLog2 /
        -- 2^wrapMaxPolySize)` pieces. The chunked FFI returns an Array
        -- of length stepChunks; reshape into `Vector stepChunks` here.
        -- For nc=1 (non-chunks2 fixtures) the array has length 1 and
        -- this is gate-identical to the pre-chunk single-point path.
        mkConstLagrangeBaseLookup \i ->
          let
            chunksArr = srsLagrangeCommitmentChunksAt vestaSrs headDomainLog2 i
          in
            case Vector.toVector @stepChunks (map coerce chunksArr) of
              Just v -> (v :: Vector _ (AffinePoint (F WrapField)))
              Nothing -> unsafeThrow
                $ "buildWrapMainConfigMulti: lagrange chunks size mismatch "
                    <> "(got "
                    <> show (Array.length chunksArr)
                    <> ", expected stepChunks="
                    <> show (reflectType (Proxy @stepChunks))
                    <> ")"
    , perBranchLagrangeAt:
        if allEqual then Nothing else Just perBranchLookup
    , blindingH: (coerce (srsBlindingGenerator vestaSrs :: AffinePoint WrapField)) :: AffinePoint (F WrapField)
    , allPossibleDomainLog2s:
        unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
    }

