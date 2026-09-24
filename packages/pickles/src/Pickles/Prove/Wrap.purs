-- | Prover-side glue for `Pickles.Wrap.Main.wrapMain`: the `WrapAdvice`
-- | record that feeds its witness generation, and the compile / solve /
-- | prove driver around it. The pure half of the wrap prover —
-- | deferred-values derivation and statement assembly — is
-- | `Pickles.Prove.Pure.Wrap`.
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
  , WrapBranchData
  , buildWrapMainConfigMulti
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Lazy as Lazy
import Data.Maybe (Maybe(..))
import Data.Newtype (over, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.Process as Process
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Types (AllocEvals, ChunkedCommitment(..), PaddedLength, PerProofUnfinalized, StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK, pallasVerifierIndexCommitments, verifierIndexDigest)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, wrapMain)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (CircuitBuilderState, Labeled, constraintsToArray)
import Snarky.Backend.Compile (SolverT, compile, makeSolver')
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, crsSize, gatesToJson)
import Snarky.Backend.Kimchi.Proof (Proof, pallasProofCommitments, pallasProofData, srsBlindingGenerator, srsLagrangeCommitmentChunksAt, vestaCreateProofWithPrev)
import Snarky.Backend.Kimchi.ProofCache (ProofCache, ProofRef, getVestaProof, setVestaProof)
import Snarky.Backend.Kimchi.Types (CRS, Gate, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.DSL (F(..), FVar, const_)
import Snarky.Circuit.Kimchi (Type1, Type2, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- Advice builder
--------------------------------------------------------------------------------

type BuildWrapAdviceInput (mpv :: Int) =
  { -- | The step proof being wrapped, in kimchi in-memory form.
    stepProof :: Proof Vesta.G StepField

  -- | Index of the step branch being wrapped.
  , whichBranch :: F WrapField

  -- | mpv unfinalized proofs decoded out of the step proof's public
  -- | input, in same-field wrap `Type2` form. A caller whose decoded
  -- | statement is in `SplitField` converts with
  -- | `fromShifted`/`toShifted`.
  , prevUnfinalizedProofs ::
      Vector mpv
        ( PerProofUnfinalized
            WrapIPARounds
            (Type2 (F WrapField))
            (F WrapField)
            Boolean
        )

  -- | The step-field Poseidon digest that sits in the step proof's
  -- | public input under `messages_for_next_step_proof`, already
  -- | cross-field coerced to `F WrapField` by the caller.
  , prevMessagesForNextStepProofHash :: F WrapField

  -- | The previous wrap proofs' step accumulators, as Vesta affines
  -- | with wrap-field coordinates. Not in the step proof's public
  -- | input: pickles carries these as private prover state. Dummy sgs
  -- | on the base case.
  , prevStepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))

  -- | Prev wrap bulletproof challenges, one stack per slot at that
  -- | slot's own width. The widths ride with the data.
  , prevOldBpChals :: Array (Array (Vector WrapIPARounds (F WrapField)))

  -- | Prev wrap proofs' polynomial evaluations, one `AllocEvals` per
  -- | proof in wrap-field scalars.
  , prevEvals :: Vector mpv (AllocEvals (F WrapField))

  -- | Domain index per prev wrap proof, into `allPossibleDomainLog2s`.
  , prevWrapDomainIndices :: Vector mpv (F WrapField)
  }

mkVestaPt
  :: AffinePoint WrapField
  -> WeierstrassAffinePoint VestaG (F WrapField)
mkVestaPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

-- | The wrap-circuit advice record for a step proof and its
-- | surrounding pickles context. Pure: the `pallas*` FFI helpers it
-- | decodes the proof with are non-effectful.
buildWrapAdvice
  :: forall @stepChunks mpv
   . Reflectable stepChunks Int
  => BuildWrapAdviceInput mpv
  -> WrapAdvice mpv stepChunks
buildWrapAdvice input =
  let
    -- One eager decode of the step proof, read by field access below.
    stepProofData = pallasProofData @StepIPARounds input.stepProof

    commits = pallasProofCommitments @stepChunks input.stepProof

    messages = WrapProofMessages
      { wComm: map (over ChunkedCommitment (map mkVestaPt)) commits.wComm
      , zComm: over ChunkedCommitment (map mkVestaPt) commits.zComm
      , tComm: map (over ChunkedCommitment (map mkVestaPt)) commits.tComm
      }

    -- The opening's `z1`/`z2` are `StepField` values, which the wrap
    -- statement stores as `Type1 (F WrapField)`: `toShifted` packs them
    -- through the cross-field
    -- `Shifted (F StepField) (Type1 (F WrapField))` instance. The
    -- commitments need none, their coordinates already being in
    -- `Vesta.BaseField = WrapField`.
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
-- The wrap prover: compile, solve, kimchi proof creation
--------------------------------------------------------------------------------

-- | Ambient data `wrapSolveAndProve` needs alongside the advice record:
-- | `wrapMain`'s compile-time config, the wrap circuit's Pallas SRS,
-- | and the packed wrap statement from `assembleWrapMainInput`, which
-- | drives both the `CircuitType` shape check and the solver input.
type WrapProveContext (branches :: Int) (mpv :: Int) (stepChunks :: Int) =
  { wrapMainConfig :: WrapMainConfig branches mpv stepChunks
  , crs :: CRS PallasG
  , publicInput ::
      Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
  , advice :: WrapAdvice mpv stepChunks
  -- | When `true`, enables the solver's prover-state debug checks and
  -- | dumps the row → label map to `/tmp/ps_wrap_row_labels.txt`.
  , debug :: Boolean
  -- | Optional disk proof-cache, threaded from `CompileMultiConfig`.
  -- | `Nothing` = no caching.
  , proofCache :: Maybe ProofCache
  -- | The cache key of the step proof being wrapped, recorded on the
  -- | wrap proof's entry so a chain is walkable from the cache alone.
  , step :: ProofRef
  -- | Kimchi-level `prev_challenges`, padded to `PaddedLength = 2`
  -- | entries. Each holds an sg (Pallas point, step-field coordinates)
  -- | and its expanded challenges.
  , kimchiPrevChallenges ::
      Vector PaddedLength
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  }

-- | Ambient data `wrapCompile` needs — a subset of `WrapProveContext`
-- | without the solver-only fields (`publicInput`, `advice`).
type WrapCompileContext :: Int -> Int -> Int -> Type
type WrapCompileContext branches mpv stepChunks =
  { wrapMainConfig :: WrapMainConfig branches mpv stepChunks
  , crs :: CRS PallasG
  -- | One `max_local_max_proofs_verified` per slot, in slot order.
  , slotWidths :: Vector mpv Int
  }

-- | Artifacts produced by `wrapCompile`. The prover and verifier
-- | indices are created here so that a caller splitting compile from
-- | solve can feed the `verifierIndex` into `buildSlotAdvice` before
-- | the solver runs.
type WrapCompileResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , gates :: Array (Gate WrapField)
  , publicInputSize :: Int
  , builtState :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
  , constraints :: Array (KimchiRow WrapField)
  -- | The per-slot widths this circuit was compiled against. The prover
  -- | reads them back from here rather than being handed them again, so
  -- | its allocation cannot disagree with the one the gates were built
  -- | for.
  , slotWidths :: Array Int
  }

-- | Artifacts produced by `wrapSolveAndProve`.
type WrapProveResult =
  { proverIndex :: ProverIndex PallasG WrapField
  , verifierIndex :: VerifierIndex PallasG WrapField
  , witness :: Vector 15 (Array WrapField)
  , publicInputs :: Array WrapField
  , proof :: Proof PallasG WrapField
  , assignments :: Assignments.Frozen WrapField
  }

-- | Monotonic counter for `KIMCHI_WRAP_CS_DUMP`'s `%c` template, bumped
-- | once per wrap-circuit compile — one per top-level rule in
-- | `compileMulti`.
wrapCsCounter :: Ref.Ref Int
wrapCsCounter = unsafePerformEffect (Ref.new 0)

bumpWrapCsCounter :: Effect Int
bumpWrapCsCounter = do
  n <- Ref.read wrapCsCounter
  Ref.write (n + 1) wrapCsCounter
  pure n

-- | Compile phase of the wrap prover: walks `wrapMain`'s circuit shape
-- | with a dummy `WrapAdvice`. Every advice read lives inside an
-- | `exists` body, which `compile` discards, so the advice record is
-- | never projected and the dummy never forced.
wrapCompile
  :: forall @branches @mpv @stepChunks numChunksPred branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
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
  => WrapCompileContext branches mpv stepChunks
  -> Effect WrapCompileResult
wrapCompile ctx = do
  let
    dummyAdvice :: WrapAdvice mpv stepChunks
    dummyAdvice = unsafeCoerce unit
  builtState <-
    compile noAdvice
      (Proxy @(Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint WrapField))
      ( \stmt -> wrapMain @branches @mpv @stepChunks ctx.wrapMainConfig stmt dummyAdvice
          ctx.slotWidths
      )

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
  csResult <- makeConstraintSystemWithPrevChallenges @WrapField
    { constraints: kimchiRows
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    , prevChallengesCount: reflectType (Proxy @PaddedLength)
    , maxPolySize: crsSize ctx.crs
    }
  let
    { gates, publicInputSize, constraints } = csResult

    -- No `cs.endo` in the argument record: `createProverIndex`'s JS
    -- implementation fetches the wrap curve's endo_base
    -- (= `Vesta.endo_base`) from the napi layer itself.
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
  -- `KIMCHI_WRAP_CS_DUMP`. `%c` in the filename template expands to a
  -- monotonic counter, so a multi-rule `compileMulti` writes one file
  -- per branch.
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
    , slotWidths: Vector.toUnfoldable ctx.slotWidths
    }

-- | Solve phase of the wrap prover: runs the solver on a compiled
-- | circuit, the real advice and the real public input, and creates the
-- | kimchi proof. Errors surface as `Either EvaluationError`. The wrap
-- | circuit emits no advice, so the row is pinned to `()` (`noAdvice`).
wrapSolveAndProve
  :: forall @branches @mpv @stepChunks numChunksPred branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
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
  => WrapProveContext branches mpv stepChunks
  -> WrapCompileResult
  -> Effect (Either EvaluationError WrapProveResult)
wrapSolveAndProve ctx compileResult = do
  let
    rawSolver
      :: SolverT WrapField (KimchiConstraint WrapField)
           ()
           (Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
           Unit
    rawSolver =
      makeSolver' { debug: ctx.debug } (Proxy @(KimchiConstraint WrapField))
        ( \stmt -> wrapMain @branches @mpv @stepChunks ctx.wrapMainConfig stmt ctx.advice
            -- Read back from the artifact the gates were built from, so
            -- the allocation here cannot disagree with that one.
            ( case Vector.toVector compileResult.slotWidths of
                Just ws -> ws
                Nothing -> unsafeThrow
                  "wrapSolveAndProve: compiled slot widths do not match mpv"
            )
        )

  eRes <- rawSolver noAdvice ctx.publicInput

  case eRes of
    Left e -> pure (Left (WithContext "wrapProve solver" e))
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
            let vkDigest = BigInt.toString (toBigInt (verifierIndexDigest compileResult.verifierIndex))
            mp <- getVestaProof cache vkDigest publicInputs
            case mp of
              Just proof -> pure proof
              Nothing -> do
                let proof = Lazy.force p
                setVestaProof cache vkDigest compileResult.verifierIndex publicInputs proof ctx.step
                pure proof
      pure $ Right
        { proverIndex: compileResult.proverIndex
        , verifierIndex: compileResult.verifierIndex
        , witness
        , publicInputs
        , proof
        , assignments
        }

-- | Write the wrap circuit's row → label map to
-- | `/tmp/ps_wrap_row_labels.txt`, so a failing row in a kimchi witness
-- | diff can be traced back to the labelled constraint that produced
-- | it. Only fires under `WrapProveContext.debug`.
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

-- | Lift a constant `StepVK WrapField` into a `StepVK (FVar
-- | WrapField)` by `const_`-ing each coordinate. `wrapMain`'s config
-- | carries step-key commitments as circuit variables so that the
-- | in-circuit `chooseKey` can scale them by a boolean.
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

-- | What the wrap circuit takes from one step branch: the rule's own
-- | `mpv`, its step domain log2 and step VK, and the wrap-domain pin of
-- | each of the circuit's `mpvMax` slots.
type WrapBranchData :: Int -> Type
type WrapBranchData mpvMax =
  { mpv :: Int
  , stepDomainLog2 :: Int
  , stepVK :: VerifierIndex VestaG StepField
  , prevWrapDomainPins :: Vector mpvMax (Maybe ProofsVerified)
  }

-- | The `WrapMainConfig` for a set of step branches, which the wrap
-- | circuit's `Pseudo.choose whichBranch` machinery dispatches over at
-- | proof time.
-- |
-- | The lagrange basis depends on the step domain, so it is filled one
-- | of two ways. When every branch shares a step domain, one basis
-- | serves all of them: `lagrangeAt` carries it and
-- | `perBranchLagrangeAt` is `Nothing`. When the domains differ,
-- | `perBranchLagrangeAt` carries one constant point per branch at each
-- | index, which the circuit 1-hot sums against `whichBranch`, and
-- | `lagrangeAt` is unused — filled from the head branch's domain only
-- | to satisfy the type.
buildWrapMainConfigMulti
  :: forall @branches @mpv @stepChunks branchesPred
   . Reflectable branches Int
  => Reflectable stepChunks Int
  => Add 1 branchesPred branches
  => CRS VestaG
  -> { perBranch :: Vector branches (WrapBranchData mpv) }
  -> WrapMainConfig branches mpv stepChunks
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
        -- Each public-input slot's lagrange basis splits into
        -- `stepChunks = ceil(2^stepDomainLog2 / 2^wrapMaxPolySize)`
        -- pieces, which the FFI returns as an `Array` to reshape here.
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
    , prevWrapDomainPins: map _.prevWrapDomainPins perBranch
    }

