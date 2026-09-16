-- | The multi-branch pickles compile: `compileMulti`, and the
-- | machinery it dispatches through.
-- |
-- | Two levels of type-level list are at work. `CompilableSpec` is
-- | indexed by one rule's prev-slot spec and supplies that rule's
-- | per-slot compile data, step advice and wrap-stage data;
-- | `CompilableRulesSpec` and `CompilableRulesSpecShape` are indexed
-- | by the list of rules and walk the branches. `RuleEntry` is one
-- | branch; `runMultiProverBody` is one branch's prover.
module Pickles.Prove.Compile
  ( PrevSlot(..)
  , SlotWrapKey(..)
  , ProverVKs
  , ProveError
  , StepInputs
  -- `Tag` carries a `Unique` as its routing key, so the name has to
  -- be reachable; nothing outside builds or inspects one.
  , Unique
  , Tag(..)
  , BranchProver(..)
  , RulesSpec
  , RulesNil
  , RulesCons
  , RuleEntry
  , mkRuleEntry
  , compileMulti
  -- Re-exported because instance resolution at user call sites needs
  -- them in scope.
  , class CompilableSpec
  , shapeCompileData
  , mkStepAdvice
  , shapeProveData
  , padShapeProveData
  , class SlotWidths
  , slotWidthsOf
  , class CompilableRulesSpec
  , branchCount
  , ruleSlotWidths
  , extractStepCompileFns
  , extractStepProveFns
  , runStepCompiles
  , buildWrapPerBranchVec
  , class CompilableRulesSpecShape
  , prePassDomainLog2s
  , class MaxOfRulesMpvs
  , class IntMax
  , class IntMaxOrd
  , runMultiCompile
  , buildBranchProvers
  , module Pickles.Verify
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Enum (fromEnum)
import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Int.Bits as Int.Bits
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over, unwrap, wrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception as Exc
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import JS.BigInt as BigInt
import Pickles.Constants (roughDomainsLog2, zkRowsForNumChunks)
import Pickles.DeferredValues (toPlonkMinimal)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (PointEval, domainGenerator, domainShifts)
import Pickles.PlonkChecks (collapseChunkedEvals, collapsePointEval)
import Pickles.ProofsVerified (boolVecToProofsVerified)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Slot (slotNumChunks, slotSourceDomainLog2s, slotWrapDomainLog2)
import Pickles.Prove.Slot as RuntimeSlot
import Pickles.Prove.Step
  ( StepAdvice(..)
  , StepCompileResult
  , StepProveContext
  , StepProveResult
  , StepRuleAt
  , preComputeStepDomainLog2
  , stepCompile
  , stepSolveAndProve
  ) as PProveStep
import Pickles.Prove.Step
  ( StepAdvice(..)
  , StepCompileResult
  , StepProveContext
  , buildSlotAdvice
  , buildStepAdvice
  , dummyWrapTockPublicInput
  , extractWrapVKCommsAdvice
  , mkDummyMsgWrapHash
  )
import Pickles.Prove.Wrap
  ( WrapCompileResult
  , buildWrapAdvice
  , buildWrapMainConfigMulti
  , wrapCompile
  , wrapSolveAndProve
  )
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Sideload.Advice(class MkUnitVkCarrier, class SideloadedVKsCarrier)
import Pickles.Sideload.Bundle (Bundle, SlotProveVk(..), projectVk, requireBundle, verifierIndex) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey(..)) as SLVK
import Pickles.Slots (Slot)
import Pickles.Step.Dummy
  ( baseCaseDummies
  , computeDummySgValues
  , dummyWrapProof
  , wrapDomainLog2ForProofsVerified
  , wrapDummyUnfinalizedProof
  )
import Pickles.Step.Dummy as Dummy
import Pickles.Step.Main (class BuildSlotVkSources)
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier, class StepSlotsTyp)
import Pickles.Step.Types as Step
import Pickles.Step.VkSource (SlotVkBlueprint(..))
import Pickles.Types (AllocEvals(..), PaddedLength, PerProofUnfinalized(..), StatementIO(..), StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (VerificationKey(..), vestaVerifierIndexCommitments)
import Pickles.Verify
  ( CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , Verifier
  , mkSomeCompiledProofWidthData
  , mkVerifier
  , prevProofDataOf
  , verify
  , wrapPublicInput
  , wrapPublicInputVP
  )
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (EQ, GT, LT)
import Prim.Ordering as PrimOrdering
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Proof
  ( pallasProofData
  , permutationVanishingPolynomial
  , proofOraclesRec
  , proverIndexDomainLog2
  , vestaProofData
  )
import Snarky.Backend.Kimchi.Proof
  ( permutationVanishingPolynomial
  , proofOraclesRec
  , proverIndexDomainLog2
  , srsBlindingGenerator
  , srsLagrangeCommitmentChunksAt
  ) as ProofFFI
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..))
import Snarky.Backend.Kimchi.ProofCache (ProofCache)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF (unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (fromShifted, toShifted) as Kimchi
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue, valueToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Snarky.Curves.Class (fromInt) as Curves
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Lagrange.Cache (LagrangeCache, pallasOps, vestaOps, warmer)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Public types
--------------------------------------------------------------------------------

type ProveError = EvaluationError

--------------------------------------------------------------------------------
-- Per-slot compile data
--------------------------------------------------------------------------------

-- | What one slot contributes to the step prover's `srsData`.
-- |
-- | `slotNc` is the chunk count of the compile that produced this
-- | slot's previous proofs, and so of its lagrange basis, which is
-- | read at the slot source's own wrap domain. The enclosing
-- | compile's wrap-VK chunk count is a different axis and does not
-- | appear here.
type SlotCompileEntry :: Int -> Type
type SlotCompileEntry slotNc =
  { fopDomainLog2s :: Array Int
  , fopZkRows :: Int
  , vkBlueprint :: SlotVkBlueprint slotNc
  }

-- | The compile-wide inputs `slotCompileEntry` needs: the subset of
-- | `CompileConfig` it reads, with the wrap-domain override already
-- | resolved.
type SlotCompileConfig =
  { pallasSrs :: CRS PallasG
  -- | The enclosing compile's declared `@stepChunks`; `Self` slots
  -- | read their previous step proof's `zk_rows` from it.
  , stepNumChunks :: Int
  -- | The enclosing rule's wrap domain log2, already resolved against
  -- | `wrapDomainOverride`. `Self` slots use it directly.
  , outerWrapDomainLog2 :: Int
  -- | The number of branches the enclosing compile has, which is the
  -- | width of every slot's `fopDomainLog2s`.
  , branchCount :: Int
  }

-- | The lagrange basis of a wrap VK at one domain, in `nc` chunks.
lagrangeAtDomain
  :: forall @nc
   . Reflectable nc Int
  => CRS PallasG
  -> Int
  -> (Int -> Vector nc (AffinePoint (F StepField)))
lagrangeAtDomain pallasSrs domainLog2 = \i ->
  let
    chunksArr = ProofFFI.srsLagrangeCommitmentChunksAt pallasSrs domainLog2 i
  in
    case Vector.toVector @nc (map coerce chunksArr) of
      Just v -> v
      Nothing -> unsafeThrow
        $ "lagrangeAtDomain: the SRS returned "
            <> show (Array.length chunksArr)
            <> " lagrange chunks at domainLog2="
            <> show domainLog2
            <> ", but this basis is declared at "
            <> show (reflectType (Proxy @nc))

-- | An external source's wrap verification key, in the commitment
-- | shape the step advice uses. The same extraction as
-- | `Pickles.Prove.Step.extractWrapVKCommsAdvice`, over any `nc`.
externalWrapVk
  :: forall @nc
   . Reflectable nc Int
  => VerifierIndex PallasG WrapField
  -> VerificationKey nc (WeierstrassAffinePoint PallasG (F StepField))
externalWrapVk vk = VerificationKey
  { sigma: map chunked comms.sigma
  , coeff: map chunked comms.coeff
  , index: map chunked comms.index
  }
  where
  comms = vestaVerifierIndexCommitments @nc vk

  wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
  wrapPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

  chunked = over ChunkedCommitment (map wrapPt)

-- | One slot's contribution. `selfStepDomainLog2s` is the enclosing
-- | compile's own per-branch step domains, which only exist after the
-- | pre-pass; `Self` slots take it verbatim.
slotCompileEntry
  :: forall @slotNc
   . Reflectable slotNc Int
  => SlotCompileConfig
  -> Array Int
  -> RuntimeSlot.Slot
  -> SlotCompileEntry slotNc
slotCompileEntry cfg selfStepDomainLog2s slot =
  { fopDomainLog2s: slotSourceDomainLog2s cfg.branchCount selfStepDomainLog2s slot
  , fopZkRows: zkRowsForNumChunks (slotNumChunks cfg.stepNumChunks slot)
  , vkBlueprint: blueprint
  }
  where
  outer = cfg.outerWrapDomainLog2

  lagrangeAt :: Int -> Int -> Vector slotNc (AffinePoint (F StepField))
  lagrangeAt = lagrangeAtDomain cfg.pallasSrs

  slotLagrange = mkConstLagrangeBaseLookup (lagrangeAt (slotWrapDomainLog2 outer slot))

  blueprint = case slot.source of
    RuntimeSlot.SelfSource -> BlueprintSelf slotLagrange
    RuntimeSlot.ExternalSource d ->
      BlueprintExternal slotLagrange (externalWrapVk @slotNc d.wrapVerifierIndex)
    -- A side-loaded slot's wrap domain is not known until prove time,
    -- so it carries all three bases and muxes in-circuit instead.
    RuntimeSlot.SideLoadedSource ->
      BlueprintSideLoaded (map lagrangeAt (13 :< 14 :< 15 :< Vector.nil))

-- | Opaque runtime identity token. Each `newUnique` allocates a
-- | globally fresh value, equal only to itself; `Tag` carries one as
-- | its routing key, and `Ord` lets it serve as a `Map` key in
-- | downstream VK registries.
newtype Unique = Unique Int

derive newtype instance Eq Unique
derive newtype instance Ord Unique

instance Show Unique where
  show (Unique n) = "Unique#" <> show n

-- | The counter behind `newUnique`. Fresh only within one JS thread,
-- | which is where a pickles compile runs.
uniqueCounter :: Ref Int
uniqueCounter = unsafePerformEffect (Ref.new 0)

newUnique :: Effect Unique
newUnique = Unique <$> Ref.modify (_ + 1) uniqueCounter

-- | The identity of one compiled rule: a `unique` routing key, fresh
-- | on every compile, and the rule's `verifier`. Produced by
-- | `compileMulti`, and supplied back alongside a proof by
-- | `InductivePrev`.
-- |
-- | The phantom `(stmt, mpv)` keep tags of different-shape rules from
-- | being substituted for each other; two same-shape rules are told
-- | apart only at runtime, by `unique`.
newtype Tag :: Type -> Int -> Type
newtype Tag stmt mpv = Tag
  { unique :: Unique
  , verifier :: Verifier
  }

derive instance Newtype (Tag stmt mpv) _

-- | One compiled rule's keys, as an `External` slot of a later
-- | compile consumes them.
type ProverVKs =
  { stepCompileResult :: StepCompileResult
  , wrapCompileResult :: WrapCompileResult
  , wrapDomainLog2 :: Int
  -- | The imported rule's declared `@stepChunks`, propagated so an
  -- | `External` slot reads it directly rather than back-deriving it
  -- | from the realized step domain log2.
  , stepNumChunks :: Int
  }

-- | Where one slot's wrap verification key comes from, chosen at
-- | compile time. This is the only place the compiled/side-loaded
-- | distinction is made.
-- |
-- | * `Self` — the slot points at the rule being compiled. The step
-- |   circuit substitutes that rule's own index, and the wrap VK
-- |   arrives as advice at prove time, because at step-compile time
-- |   the wrap circuit does not exist yet.
-- | * `External vks` — a previously compiled rule, whose `ProverVKs`
-- |   the user supplies. Its wrap VK is baked into the step circuit
-- |   as a constant, so that slot needs no advice path.
-- | * `SideLoadedKey` — no compile-time key at all. The wrap VK
-- |   arrives as a runtime witness in `StepInputs.sideloadedVKs` and
-- |   is allocated in-circuit; compile time fixes only the slot's
-- |   `n`, the upper bound on its `max_proofs_verified`.
data SlotWrapKey
  = Self
  | External ProverVKs
  | SideLoadedKey

type StepInputs :: Type -> Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier vkCarrier =
  { appInput :: inputVal
  , prevs :: prevsCarrier
  -- | One `SlotProveVk` per slot, in slot order. A `SideLoadedKey`
  -- | slot must be given `SideLoadedVk` with its runtime bundle; a
  -- | bundle supplied for a `Self` or `External` slot is refused
  -- | rather than ignored.
  , sideloadedVKs :: vkCarrier
  }

-- | What the caller supplies for one prev slot at prove time.
-- |
-- | * `BasePrev` — no previous proof for this slot. Its
-- |   `dummyStatement` is circuit-irrelevant, since the slot's
-- |   `proofMustVerify` is `false`, but it still fills that slot's
-- |   entry of `prevAppStates` in advice, so it has to typecheck as
-- |   the prev rule's full statement.
-- | * `InductivePrev` — a real previous proof, together with the
-- |   `Tag` of the rule that produced it.
-- |
-- | The slot's `n` is the outer `max_proofs_verified`, not the prev
-- | rule's own width: `CompiledProof` hides that width inside
-- | `widthData`, so `n` is the same across every branch's proofs.
data PrevSlot :: Type -> Int -> Type -> Type
data PrevSlot inputVal n stmt
  = BasePrev { dummyStatement :: stmt }
  | InductivePrev
      (CompiledProof n stmt)
      (Tag stmt n)

type CompileConfig :: Int -> Type
type CompileConfig mpv =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -- | Where each slot's wrap VK comes from, in slot order. The length
  -- | is in the type, so a rule that supplies the wrong number of
  -- | keys is a type error rather than a runtime one.
  , perSlotImportedVKs :: Vector mpv SlotWrapKey
  , debug :: Boolean
  -- | The compile's declared `@stepChunks`, one value for every
  -- | branch. `Self` slots read their prev step proof's `zk_rows`
  -- | from it.
  , stepNumChunks :: Int
  -- | The wrap domain this compile's own wrap circuit is assumed to
  -- | have. One value for the whole compile, so a `Self` prev slot,
  -- | which verifies a proof of this very system, reads it directly
  -- | instead of deriving a domain of its own.
  , selfWrapDomainLog2 :: Int
  -- | Optional disk proof-cache (test/dev). `Nothing` = no caching.
  , proofCache :: Maybe ProofCache
  }

-- | The compile's wrap domain: the override when given, otherwise the
-- | three-entry table applied to `max_proofs_verified`.
-- |
-- | Nothing here measures the wrap circuit, so the table is a guess.
-- | When it misses, the check after `wrapCompile` reports it, and the
-- | override is how it is corrected.
resolveSelfWrapDomainLog2 :: Int -> Maybe Int -> Int
resolveSelfWrapDomainLog2 mpvMax = case _ of
  Just o -> o
  Nothing -> wrapDomainLog2ForProofsVerified mpvMax

-- | One slot's compile-time key, as the runtime slot record the
-- | per-slot derivations in `Pickles.Prove.Slot` read.
runtimeSlotOf :: Int -> SlotWrapKey -> RuntimeSlot.Slot
runtimeSlotOf localMpv key =
  { localMpv
  , source: case key of
      Self -> RuntimeSlot.SelfSource
      SideLoadedKey -> RuntimeSlot.SideLoadedSource
      External vks -> RuntimeSlot.ExternalSource
        { wrapVerifierIndex: vks.wrapCompileResult.verifierIndex
        , wrapDomainLog2: vks.wrapDomainLog2
        -- Only single-rule external sources are supported; the one
        -- domain is replicated to the branch width by
        -- `slotSourceDomainLog2s`.
        , stepDomainLog2s:
            NonEmptyArray.singleton
              (ProofFFI.proverIndexDomainLog2 vks.stepCompileResult.proverIndex)
        , numChunks: vks.stepNumChunks
        }
  }

-- | A side-loaded slot's wrap domain log2, decoded from its runtime
-- | VK descriptor's length-3 one-hot `actualWrapDomainSize` vector.
bundleWrapDomainLog2 :: forall nc. SideloadBundle.Bundle nc -> Int
bundleWrapDomainLog2 bundle =
  Dummy.wrapDomainLog2ForProofsVerified
    ( fromEnum
        ( boolVecToProofsVerified
            ( case SideloadBundle.projectVk bundle of
                SLVK.VerificationKey vkRec -> vkRec.actualWrapDomainSize
            )
        )
    )

-- | One slot's contribution to `shapeCompileData`: its per-slot
-- | entries spliced onto the tail, plus the rule-wide fields.
-- |
-- | `slotNc` stays a type variable because a slot's chunk count
-- | belongs to the compile that produced its previous proofs, so two
-- | slots of one rule can differ.
consShapeCompileData
  :: forall prevsSpec slotNc mpv restMpv nd restBlueprints
   . Add restMpv 1 mpv
  => Reflectable mpv Int
  => Reflectable nd Int
  => Reflectable slotNc Int
  => CompileConfig prevsSpec
  -> Vector nd Int
  -> RuntimeSlot.Slot
  -> ShapeCompileData restMpv nd restBlueprints
  -> ShapeCompileData mpv nd (SlotVkBlueprint slotNc /\ restBlueprints)
consShapeCompileData cfg selfStepDomainLog2s headSlot restShape =
  { stepProveCtx:
      { srsData:
          { blindingH:
              coerce (ProofFFI.srsBlindingGenerator cfg.srs.pallasSrs :: AffinePoint StepField)
          , perSlotFopDomainLog2s:
              headFopDomainLog2s
                :< restShape.stepProveCtx.srsData.perSlotFopDomainLog2s
          , perSlotFopZkRows:
              headEntry.fopZkRows :< restShape.stepProveCtx.srsData.perSlotFopZkRows
          , perSlotVkBlueprints:
              headEntry.vkBlueprint
                /\ restShape.stepProveCtx.srsData.perSlotVkBlueprints
          }
      , dummySg: outerDummySgs.ipa.wrap.sg
      , crs: cfg.srs.vestaSrs
      , debug: cfg.debug
      , proofCache: cfg.proofCache
      }
  , wrapDomainLog2: cfg.selfWrapDomainLog2
  }
  where
  headEntry = slotCompileEntry
    { pallasSrs: cfg.srs.pallasSrs
    , stepNumChunks: cfg.stepNumChunks
    , outerWrapDomainLog2: cfg.selfWrapDomainLog2
    , branchCount: Vector.length selfStepDomainLog2s
    }
    (Vector.toUnfoldable selfStepDomainLog2s)
    headSlot

  headFopDomainLog2s = case Vector.toVector headEntry.fopDomainLog2s of
    Just v -> v
    Nothing -> unsafeThrow
      $ "shapeCompileData: slot step-domain count "
          <> show (Array.length headEntry.fopDomainLog2s)
          <> " does not match the branch count "
          <> show (Vector.length selfStepDomainLog2s)

  outerBcd = Dummy.baseCaseDummies
    { maxProofsVerified: reflectType (Proxy :: Proxy mpv) }
  outerDummySgs =
    Dummy.computeDummySgValues outerBcd cfg.srs.pallasSrs cfg.srs.vestaSrs

-- | What one slot contributes to the step prover's advice, spliced
-- | onto the tail.
-- |
-- | The tail arrives as an unforced `Effect`: this slot's oracle work
-- | has to run before the tail's.
consMkStepAdvice
  :: forall @w wPad inputVal input prevHeadInput prevHeadStmt
       prevHeadStmtVar prevsSpec restSpec restLen len headVkCell
       restCarrier restValCarrier restVkCarrier
   . Reflectable w Int
  => Compare w 3 LT
  => Reflectable wPad Int
  => Add wPad w PaddedLength
  => Add restLen 1 len
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -> inputVal
  -> { slotWrapVK :: VerifierIndex PallasG WrapField
     , slotWrapDomainLog2 :: Int
     , slotStepDomainLog2 :: Int
     , slotStepZkRows :: Int
     , slotWrapZkRows :: Int
     }
  -> headVkCell
  -> PrevSlot prevHeadInput w prevHeadStmt
  -> Effect
       { stepAdvice ::
           StepAdvice restSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal
             restLen
             restCarrier
             restValCarrier
             restVkCarrier
       , challengePolynomialCommitments :: Vector restLen (AffinePoint StepField)
       , baseCaseWrapPublicInputs :: Vector restLen (Array WrapField)
       }
  -> Effect
       { stepAdvice ::
           StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal
             len
             ( Step.PerProofWitness WrapVkChunks StepIPARounds WrapIPARounds
                 (F StepField)
                 (Type2 (SplitField (F StepField) Boolean))
                 Boolean
                 /\ restCarrier
             )
             (prevHeadStmt /\ restValCarrier)
             (headVkCell /\ restVkCarrier)
       , challengePolynomialCommitments :: Vector len (AffinePoint StepField)
       , baseCaseWrapPublicInputs :: Vector len (Array WrapField)
       }
consMkStepAdvice srs appInput slotParams headVkCell headSlot restEffect = do
  contrib <- buildSlotAdvice @w
    { publicInput: appInput
    , prevStatement: slotData.prevStatement
    , wrapDomainLog2: slotParams.slotWrapDomainLog2
    , stepDomainLog2: slotParams.slotStepDomainLog2
    , stepZkRows: slotParams.slotStepZkRows
    , wrapZkRows: slotParams.slotWrapZkRows
    , wrapVK: slotParams.slotWrapVK
    , stepOpeningSg: slotData.stepOpeningSg
    , kimchiPrevSg: slotData.kimchiPrevSg
    , wrapProof: slotData.wrapProof
    , wrapPublicInput: slotData.wrapPublicInputArr
    , prevChalPolys: slotData.prevChalPolys
    , wrapPlonkRaw: slotData.wrapPlonkRaw
    , wrapPrevEvals: slotData.wrapPrevEvals
    , wrapBranchData: slotData.wrapBranchData
    , wrapSpongeDigest: slotData.wrapSpongeDigest
    , mustVerify: slotData.mustVerify
    , wrapOwnPaddedBpChals: slotData.wrapOwnPaddedBpChals
    , fopState: slotData.fopState
    , stepAdvicePrevEvals: slotData.stepAdvicePrevEvals
    , kimchiPrevChallengesExpanded: slotData.kimchiPrevChallengesExpanded
    , prevChallengesForStepHash: slotData.prevChallengesForStepHash
    }

  restResult <- restEffect

  let
    StepAdvice restA = restResult.stepAdvice
    combinedAdvice = StepAdvice
      { perProofSlotsCarrier: contrib.slotSppw /\ restA.perProofSlotsCarrier
      , publicInput: appInput
      , publicUnfinalizedProofs:
          contrib.slotUnfinalized :< restA.publicUnfinalizedProofs
      , messagesForNextWrapProof:
          contrib.slotMsgWrapHashStep :< restA.messagesForNextWrapProof
      , messagesForNextWrapProofDummyHash: restA.messagesForNextWrapProofDummyHash
      -- The wrap VK is compile-wide constant, so the tail's is
      -- propagated unchanged.
      , wrapVerifierIndex: restA.wrapVerifierIndex
      , kimchiPrevChallenges:
          contrib.slotKimchiPrevEntry :< restA.kimchiPrevChallenges
      , prevAppStates: slotData.prevStatement /\ restA.prevAppStates
      , sideloadedVKs: headVkCell /\ restA.sideloadedVKs
      }
  pure
    { stepAdvice: combinedAdvice
    , challengePolynomialCommitments:
        contrib.challengePolynomialCommitment :< restResult.challengePolynomialCommitments
    , baseCaseWrapPublicInputs:
        slotData.wrapPublicInputArr :< restResult.baseCaseWrapPublicInputs
    }
  where
  slotW = reflectType (Proxy :: Proxy w)

  -- Slot-specific dummies sized by this slot's own width, not the
  -- enclosing rule's.
  bcd = Dummy.baseCaseDummies { maxProofsVerified: slotW }
  dummySgs = Dummy.computeDummySgValues bcd srs.pallasSrs srs.vestaSrs
  dummyWrapSg = dummySgs.ipa.wrap.sg
  dummyStepSg = dummySgs.ipa.step.sg

  proofsVerifiedMask = (slotW >= 2) :< (slotW >= 1) :< Vector.nil

  stepEndoScalarF =
    let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

  slotData = case headSlot of
    BasePrev { dummyStatement } ->
      let
        baseCaseDummyChalPoly =
          { sg: dummyWrapSg, challenges: dummyIpaChallenges.wrapExpanded }

        msgWrapDigest = hashMessagesForNextWrapProofPureGeneral
          { sg: dummyStepSg
          , paddedChallenges:
              Vector.replicate @PaddedLength dummyIpaChallenges.wrapExpanded
          }

        fopProofState = Dummy.stepDummyUnfinalizedProof @w bcd
          { domainLog2: Dummy.wrapDomainLog2ForProofsVerified slotW }
          (map SizedF.wrapF bcd.ipaStepChallenges)

        baseCaseWrapPI = dummyWrapTockPublicInput @w
          { stepDomainLog2: slotParams.slotStepDomainLog2
          , wrapVK: slotParams.slotWrapVK
          , prevStatement: dummyStatement
          , wrapSg: dummyWrapSg
          , stepSg: dummyStepSg
          , msgWrapDigest
          , fopProofState
          }
      in
        { prevStatement: dummyStatement
        , stepOpeningSg: dummyStepSg
        , kimchiPrevSg: dummyStepSg
        , wrapProof: dummyWrapProof bcd
        , wrapPublicInputArr: baseCaseWrapPI
        , prevChalPolys:
            Vector.replicate @PaddedLength baseCaseDummyChalPoly
        , wrapPlonkRaw:
            { alpha: bcd.proofDummy.plonk.alpha
            , beta: bcd.proofDummy.plonk.beta
            , gamma: bcd.proofDummy.plonk.gamma
            , zeta: bcd.proofDummy.plonk.zeta
            }
        , wrapPrevEvals: bcd.proofDummy.prevEvals
        , wrapBranchData:
            -- `domainLog2` of a wrap statement's branch data holds the
            -- prev's step domain, not its wrap domain; that is what
            -- `expandDeferredForVerify` reads back.
            { domainLog2: (Curves.fromInt slotParams.slotStepDomainLog2 :: StepField)
            , proofsVerifiedMask
            }
        , wrapSpongeDigest: (zero :: StepField)
        , mustVerify: false
        , wrapOwnPaddedBpChals:
            Vector.replicate @PaddedLength dummyIpaChallenges.wrapExpanded
        , fopState: fopProofState
        , stepAdvicePrevEvals: bcd.proofDummy.prevEvals
        , kimchiPrevChallengesExpanded: dummyIpaChallenges.stepExpanded
        , prevChallengesForStepHash:
            Vector.replicate dummyIpaChallenges.stepExpanded
        }
    InductivePrev prevCp prevTag ->
      let
        CompiledProof prevRaw = prevCp
        Tag { verifier: prevVerifier } = prevTag

        -- The previous proof as the recursive prover needs it:
        -- width-erased, with the constants it is judged against. See
        -- `Pickles.Verify.PrevProofData`.
        prevData = prevProofDataOf prevVerifier prevCp

        prevStepBpChalsExpanded =
          map
            ( \sc ->
                toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                  stepEndoScalarF
            )
            prevData.proof.rawBulletproofChallenges

        wrapPI = wrapPublicInputVP prevVerifier prevData.proof

        prevZetaField =
          coerce
            (toFieldPure prevData.proof.rawPlonk.zeta (F prevVerifier.stepEndo))

        -- A step domain is per-branch, so it comes off the prev proof
        -- rather than off the `Verifier`.
        prevStepGenerator = domainGenerator prevData.proof.stepDomainLog2

        prevStepShifts = domainShifts prevData.proof.stepDomainLog2

        prevVanishesOnZk = ProofFFI.permutationVanishingPolynomial
          { domainLog2: prevData.proof.stepDomainLog2
          , zkRows: prevVerifier.stepZkRows
          , pt: prevZetaField
          }

        -- The unpadded accumulators, reified back to a `Vector n`.
        -- `expandDeferredForVerify` folds over them, so the length has
        -- to be the proof's real width: padding here would change both
        -- the challenges digest and the combined inner product.
        prevDv = Vector.reifyVector prevData.proof.oldBulletproofChallenges
          \prevOldBpChals -> expandDeferredForVerify
            { rawPlonk: prevData.proof.rawPlonk
            , rawBulletproofChallenges: prevData.proof.rawBulletproofChallenges
            , branchData: prevData.proof.branchData
            , spongeDigestBeforeEvaluations:
                prevData.proof.spongeDigestBeforeEvaluations
            , chunkedEvals: prevData.proof.prevEvalsChunked
            , pEval0Chunks: prevData.proof.pEval0Chunks
            , oldBulletproofChallenges: prevOldBpChals
            , domainLog2: prevData.proof.stepDomainLog2
            , zkRows: prevVerifier.stepZkRows
            , srsLengthLog2: prevVerifier.stepSrsLengthLog2
            , generator: prevStepGenerator
            , shifts: prevStepShifts
            , vanishesOnZk: prevVanishesOnZk
            , omegaForLagrange: \_ -> one
            , endo: prevVerifier.stepEndo
            , linearizationPoly: prevVerifier.linearizationPoly
            }

        prevPaddedChalPolys
          :: Vector PaddedLength
               { sg :: AffinePoint StepField
               , challenges :: Vector WrapIPARounds WrapField
               }
        prevPaddedChalPolys = Vector.zipWith
          (\sg ch -> { sg, challenges: ch })
          prevData.padded.outerStepChalPolyCommsPadded
          prevData.padded.msgWrapChallengesPadded

        fopState =
          { deferredValues:
              { plonk: prevDv.plonk
              , combinedInnerProduct: prevDv.combinedInnerProduct
              , xi: prevDv.xi
              , bulletproofChallenges: prevDv.bulletproofPrechallenges
              , b: prevDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations:
              F prevDv.spongeDigestBeforeEvaluations
          }
      in
        { prevStatement: prevRaw.statement
        , stepOpeningSg: prevData.proof.challengePolynomialCommitment
        , kimchiPrevSg: prevData.proof.challengePolynomialCommitment
        , wrapProof: prevData.proof.wrapProof
        , wrapPublicInputArr: wrapPI
        , prevChalPolys: prevPaddedChalPolys
        , wrapPlonkRaw:
            { alpha: SizedF.unwrapF prevDv.plonk.alpha
            , beta: SizedF.unwrapF prevDv.plonk.beta
            , gamma: SizedF.unwrapF prevDv.plonk.gamma
            , zeta: SizedF.unwrapF prevDv.plonk.zeta
            }
        , wrapPrevEvals: prevData.prevEvals
        , wrapBranchData: prevData.proof.branchData
        , wrapSpongeDigest: prevData.proof.spongeDigestBeforeEvaluations
        , mustVerify: true
        , wrapOwnPaddedBpChals: prevData.padded.msgWrapChallengesPadded
        , fopState
        , stepAdvicePrevEvals: prevData.prevEvals
        , kimchiPrevChallengesExpanded: prevStepBpChalsExpanded
        , prevChallengesForStepHash: prevData.padded.oldBulletproofChallengesPadded
        }

-- | What one slot contributes to the wrap prover's inputs, spliced
-- | onto the tail.
-- |
-- | `slotParams` is everything that varies by slot source: the wrap
-- | verifier index, the wrap domain, the slot's width and the padding
-- | that width implies. A compiled slot resolves them from the
-- | enclosing or the imported compile, a side-loaded slot off its
-- | runtime key.
consShapeProveData
  :: forall prevHeadInput prevHeadOutput slotWidth mpv restMpv
   . Add 1 restMpv mpv
  => Add restMpv 1 mpv
  => { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -> { slotWrapVK :: VerifierIndex PallasG WrapField
     , slotWrapDomainLog2 :: Int
     , slotWidth :: Int
     , slotPad :: Int
     }
  -> ShapeProveSideInfo mpv
  -> PrevSlot prevHeadInput slotWidth (StatementIO prevHeadInput prevHeadOutput)
  -> ShapeProveData restMpv
  -> ShapeProveData mpv
consShapeProveData srs slotParams sideInfo headSlot restProveData =
  { prevSgs: slotData.prevSg :< restProveData.prevSgs
  , prevStepChallenges:
      slotData.prevStepChals :< restProveData.prevStepChallenges
  , msgWrapChallenges:
      msgForNextWrapRealChals :< restProveData.msgWrapChallenges
  , prevUnfinalizedProofs: headUnfinalizedWrap :< restProveData.prevUnfinalizedProofs
  , prevStepAccs: slotData.prevStepAcc :< restProveData.prevStepAccs
  , prevEvals: slotData.headPrevEvals :< restProveData.prevEvals
  -- The index is into `Pickles.Prove.Wrap`'s
  -- `allPossibleDomainLog2s = [13, 14, 15]`, hence `log2 - 13`.
  , prevWrapDomainIndices:
      F (Curves.fromInt (slotParams.slotWrapDomainLog2 - 13) :: WrapField)
        :< restProveData.prevWrapDomainIndices
  , kimchiPrevEntries:
      { sgX: (unwrap headChalPolyComm).x
      , sgY: (unwrap headChalPolyComm).y
      , challenges: msgForNextWrapRealChals
      } :< restProveData.kimchiPrevEntries
  , slotsValue:
      Array.cons slotData.headSlotPrevWrapBpChals restProveData.slotsValue
  }
  where
  -- Dummies sized by the slot's own width, not the enclosing rule's:
  -- a rule's slots can have different widths, and each slot's dummies
  -- have to match its own.
  bcd = Dummy.baseCaseDummies { maxProofsVerified: slotParams.slotWidth }
  dummySgs = Dummy.computeDummySgValues bcd srs.pallasSrs srs.vestaSrs
  stepSgD = dummySgs.ipa.step.sg -- AffinePoint WrapField

  { head: PerProofUnfinalized headUnfRaw, tail: _ } =
    Vector.uncons sideInfo.unfinalizedSlots
  { head: headChalPolyComm, tail: _ } =
    Vector.uncons sideInfo.challengePolynomialCommitments
  { head: headBaseCaseWrapPI, tail: _ } =
    Vector.uncons sideInfo.baseCaseWrapPublicInputs

  -- Type1 to Type2 cross-field coerce of the raw step-advice
  -- unfinalized entry into the wrap-advice shape, field by field.
  headUnfinalizedWrap
    :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean
  headUnfinalizedWrap = PerProofUnfinalized
    { combinedInnerProduct:
        Kimchi.toShifted (Kimchi.fromShifted headUnfRaw.combinedInnerProduct :: F WrapField)
    , b: Kimchi.toShifted (Kimchi.fromShifted headUnfRaw.b :: F WrapField)
    , zetaToSrsLength:
        Kimchi.toShifted (Kimchi.fromShifted headUnfRaw.zetaToSrsLength :: F WrapField)
    , zetaToDomainSize:
        Kimchi.toShifted (Kimchi.fromShifted headUnfRaw.zetaToDomainSize :: F WrapField)
    , perm: Kimchi.toShifted (Kimchi.fromShifted headUnfRaw.perm :: F WrapField)
    , spongeDigest:
        over F crossFieldDigest headUnfRaw.spongeDigest
    , beta: over UnChecked coerceViaBits headUnfRaw.beta
    , gamma: over UnChecked coerceViaBits headUnfRaw.gamma
    , alpha: over UnChecked coerceViaBits headUnfRaw.alpha
    , zeta: over UnChecked coerceViaBits headUnfRaw.zeta
    , xi: over UnChecked coerceViaBits headUnfRaw.xi
    , bulletproofChallenges:
        map (over UnChecked coerceViaBits) headUnfRaw.bulletproofChallenges
    , shouldFinalize: headUnfRaw.shouldFinalize
    }

  wrapEndoScalar =
    let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

  msgForNextWrapRealChals =
    map
      ( \(UnChecked v) ->
          toFieldPure (coerceViaBits v :: SizedF 128 WrapField) wrapEndoScalar
      )
      headUnfRaw.bulletproofChallenges

  stepEndoScalarF =
    let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

  slotData = case headSlot of
    BasePrev _ ->
      let
        -- The dummy wrap proof carries no public evaluation of its
        -- own, so the public eval is the oracle's recomputed x_hat:
        -- run the oracle on the dummy with its wrap public input and
        -- the base-case dummy prev challenges, the same inputs the
        -- step finalize sees.
        dummyWrapXhat =
          ( ProofFFI.proofOraclesRec slotParams.slotWrapVK
              { proof: dummyWrapProof bcd
              , publicInput: headBaseCaseWrapPI
              , prevChallenges:
                  Vector.toUnfoldable
                    ( Vector.replicate @PaddedLength
                        { sgX: (unwrap dummySgs.ipa.wrap.sg).x
                        , sgY: (unwrap dummySgs.ipa.wrap.sg).y
                        , challenges:
                            ( Vector.toUnfoldable dummyIpaChallenges.wrapExpanded
                                :: Array WrapField
                            )
                        }
                    )
              }
          ).publicEvals
        de = bcd.dummyEvals
        pe = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
        headPrevEvals = AllocEvals
          { ftEval1: F de.ftEval1
          , publicEvals:
              { zeta: F dummyWrapXhat.zeta
              , omegaTimesZeta: F dummyWrapXhat.omegaTimesZeta
              }
          , zEvals: pe de.zEvals
          , witnessEvals: map pe de.witnessEvals
          , coeffEvals: map pe de.coeffEvals
          , sigmaEvals: map pe de.sigmaEvals
          , indexEvals: map pe de.indexEvals
          }
      in
        { prevSg: stepSgD
        , prevStepChals: dummyIpaChallenges.stepExpanded
        , prevStepAcc: WeierstrassAffinePoint { x: F (unwrap stepSgD).x, y: F (unwrap stepSgD).y }
        , headPrevEvals
        , headSlotPrevWrapBpChals:
            Array.replicate slotParams.slotWidth
              (map F dummyIpaChallenges.wrapExpanded)
        }
    InductivePrev prevCp prevTag ->
      let
        Tag { verifier: prevVerifier } = prevTag

        -- Only the padded accumulators are needed here, so unlike in
        -- `mkStepAdvice` there is no unpadded vector to reify.
        prevData = prevProofDataOf prevVerifier prevCp

        prevStepBpChalsExpanded =
          map
            ( \sc ->
                toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                  stepEndoScalarF
            )
            prevData.proof.rawBulletproofChallenges

        prevWrapPI = wrapPublicInputVP prevVerifier prevData.proof

        -- Kimchi's `prev_challenges` argument is a flat array of
        -- `PaddedLength` entries, so the padded `Vector`s are zipped
        -- and converted to `Array` once, here at the boundary. The
        -- coordinates are `StepField` because a Pallas point's
        -- coordinates live in Vesta's scalar field.
        prevWrapKimchiPrevChals
          :: Array
               { sgX :: StepField
               , sgY :: StepField
               , challenges :: Array WrapField
               }
        prevWrapKimchiPrevChals = Vector.toUnfoldable $
          Vector.zipWith
            ( \(AffinePoint sg) ch ->
                { sgX: sg.x
                , sgY: sg.y
                , challenges: Vector.toUnfoldable ch
                }
            )
            prevData.padded.outerStepChalPolyCommsPadded
            prevData.padded.msgWrapChallengesPadded

        prevWrapOracles =
          ProofFFI.proofOraclesRec slotParams.slotWrapVK
            { proof: prevData.proof.wrapProof
            , publicInput: prevWrapPI
            , prevChallenges: prevWrapKimchiPrevChals
            }

        peWF = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
        prevWrapCollapse = collapsePointEval
          { rounds: reflectType (Proxy :: Proxy WrapIPARounds)
          , zeta: prevWrapOracles.zeta
          , zetaOmega:
              prevWrapOracles.zeta * domainGenerator slotParams.slotWrapDomainLog2
          }
        prevWrapData = vestaProofData @WrapIPARounds prevData.proof.wrapProof
        prevHeadPrevEvals = AllocEvals
          { ftEval1: F prevWrapOracles.ftEval1
          , publicEvals:
              let
                pew = prevWrapOracles.publicEvals
              in
                { zeta: F pew.zeta, omegaTimesZeta: F pew.omegaTimesZeta }
          , zEvals: peWF (prevWrapCollapse prevWrapData.evals.z)
          , witnessEvals:
              map (peWF <<< prevWrapCollapse) prevWrapData.evals.w
          , coeffEvals:
              map (peWF <<< prevWrapCollapse) prevWrapData.evals.coefficients
          , sigmaEvals:
              map (peWF <<< prevWrapCollapse) prevWrapData.evals.s
          , indexEvals:
              map (peWF <<< prevWrapCollapse) prevWrapData.evals.indexEvals
          }

        -- The slot's own stacks, recovered by dropping the prepended
        -- dummies from the padded form.
        headSlotPrevWrapBpChals
          :: Array (Vector WrapIPARounds (F WrapField))
        headSlotPrevWrapBpChals =
          Array.drop slotParams.slotPad
            ( Vector.toUnfoldable
                (map (map F) prevData.padded.msgWrapChallengesPadded)
            )
      in
        { prevSg: prevData.proof.challengePolynomialCommitment
        , prevStepChals: prevStepBpChalsExpanded
        , prevStepAcc: WeierstrassAffinePoint
            { x: F (unwrap prevData.proof.challengePolynomialCommitment).x
            , y: F (unwrap prevData.proof.challengePolynomialCommitment).y
            }
        , headPrevEvals: prevHeadPrevEvals
        , headSlotPrevWrapBpChals
        }

-- | What `shapeCompileData` returns: the step solver's context and
-- | the compile's wrap domain log2 (13, 14 or 15, for `mpv` 0, 1, 2).
-- | Both are derived from the `prevsSpec` shape and the
-- | `perSlotImportedVKs` alone, never from the rule or a prove call's
-- | inputs.
type ShapeCompileData :: Int -> Int -> Type -> Type
type ShapeCompileData mpv nd blueprints =
  { stepProveCtx :: StepProveContext mpv nd blueprints
  , wrapDomainLog2 :: Int
  }

-- | What `shapeProveData` needs out of `mkStepAdvice`'s return, one
-- | entry per slot.
-- |
-- | * `challengePolynomialCommitments` — the outer step proofs'
-- |   opening sgs, which feed each slot's kimchi-prev entry.
-- | * `unfinalizedSlots` — the step-field unfinalized proofs, which
-- |   `shapeProveData` coerces into `prevUnfinalizedProofs`.
-- | * `baseCaseWrapPublicInputs` — the serialized
-- |   `dummyWrapTockPublicInput` a base-case slot feeds to
-- |   `proofOraclesRec`, so its recomputed evals are the ones the
-- |   step circuit saw. Per-slot, because slots of one rule can have
-- |   differently shaped prev-rule wrap statements.
type ShapeProveSideInfo :: Int -> Type
type ShapeProveSideInfo mpv =
  { challengePolynomialCommitments :: Vector mpv (AffinePoint StepField)
  , unfinalizedSlots ::
      Vector mpv
        ( PerProofUnfinalized WrapIPARounds
            (Type2 (SplitField (F StepField) Boolean))
            (F StepField)
            Boolean
        )
  , baseCaseWrapPublicInputs :: Vector mpv (Array WrapField)
  }

-- | The per-slot data the wrap stage is built from, one entry per
-- | slot of one rule. `padShapeProveData` widens it to the wrap
-- | circuit's `mpvMax`.
type ShapeProveData :: Int -> Type
type ShapeProveData mpv =
  { prevSgs :: Vector mpv (AffinePoint WrapField)
  , prevStepChallenges :: Vector mpv (Vector StepIPARounds StepField)
  , msgWrapChallenges :: Vector mpv (Vector WrapIPARounds WrapField)
  , prevUnfinalizedProofs ::
      Vector mpv
        (PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean)
  , prevStepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  , prevEvals :: Vector mpv (AllocEvals (F WrapField))
  , prevWrapDomainIndices :: Vector mpv (F WrapField)
  , kimchiPrevEntries ::
      Vector mpv
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  -- | Each prev's wrap bulletproof challenge stacks, in slot order.
  , slotsValue :: Array (Array (Vector WrapIPARounds (F WrapField)))
  }

--------------------------------------------------------------------------------
-- padShapeProveData
--------------------------------------------------------------------------------

-- | One entry's worth of each field `padShapeProveData` front-pads,
-- | built by `runMultiProverBody` from the wrap circuit's dummies and
-- | SRS-derived sg values.
type PadProveDataDummies =
  { dummyPrevSg :: AffinePoint WrapField
  , dummyPrevStepChals :: Vector StepIPARounds StepField
  , dummyMsgWrapChal :: Vector WrapIPARounds WrapField
  , dummyPrevUnfinalizedProof ::
      PerProofUnfinalized
        WrapIPARounds
        (Type2 (F WrapField))
        (F WrapField)
        Boolean
  , dummyPrevStepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
  , dummyPrevEvals :: AllocEvals (F WrapField)
  , dummyPrevWrapDomainIdx :: F WrapField
  , dummyKimchiPrevEntry ::
      { sgX :: StepField
      , sgY :: StepField
      , challenges :: Vector WrapIPARounds WrapField
      }
  , dummySlotChal :: Vector WrapIPARounds (F WrapField)
  }

-- | Pad a `ShapeProveData mpv` to `ShapeProveData mpvMax` by
-- | front-padding each field with `mpvPad = mpvMax - mpv` copies of
-- | the corresponding dummy. At `mpv = mpvMax` every `replicate @0`
-- | is empty and every append the identity, so that case needs no
-- | branch of its own.
padShapeProveData
  :: forall mpv mpvPad mpvMax
   . Add mpvPad mpv mpvMax
  => Reflectable mpvPad Int
  => PadProveDataDummies
  -- | The wrap circuit's per-slot `max_local_max_proofs_verified`, in
  -- | slot order. Front-padding fills the first `mpvPad` of these, and
  -- | each dummy slot's stack must be exactly as wide as the slot the
  -- | wrap circuit allocated — see `slotsValue` below.
  -> Array Int
  -> ShapeProveData mpv
  -> ShapeProveData mpvMax
padShapeProveData dummies slotWidths sd =
  { prevSgs:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevSg)
        sd.prevSgs
  , prevStepChallenges:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevStepChals)
        sd.prevStepChallenges
  , msgWrapChallenges:
      Vector.append (Vector.replicate @mpvPad dummies.dummyMsgWrapChal)
        sd.msgWrapChallenges
  , prevUnfinalizedProofs:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevUnfinalizedProof)
        sd.prevUnfinalizedProofs
  , prevStepAccs:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevStepAcc)
        sd.prevStepAccs
  , prevEvals:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevEvals)
        sd.prevEvals
  , prevWrapDomainIndices:
      Vector.append (Vector.replicate @mpvPad dummies.dummyPrevWrapDomainIdx)
        sd.prevWrapDomainIndices
  , kimchiPrevEntries:
      Vector.append (Vector.replicate @mpvPad dummies.dummyKimchiPrevEntry)
        sd.kimchiPrevEntries
  -- Front-pad the slot list itself: a rule with fewer slots than the
  -- wrap circuit's `mpvMax` contributes dummy stacks for the missing
  -- ones, each as wide as the slot the wrap circuit allocated.
  -- `Pickles.Wrap.Main` allocates `oldBpChals` through `perSlotTyp
  -- widths` and assigns from the value's fields, so a dummy narrower
  -- than its slot leaves the tail variables unassigned — which the
  -- solver reports as `MissingVariable` from inside `b-poly`.
  , slotsValue:
      map (\w -> Array.replicate w dummies.dummySlotChal)
        (Array.take (reflectType (Proxy @mpvPad)) slotWidths)
        <> sd.slotsValue
  }

--------------------------------------------------------------------------------
-- CompilableSpec — the shape-dependent dispatch class
--------------------------------------------------------------------------------

-- | One rule's prev-slot spec, and the three pieces of per-slot data
-- | derived from it: compile-time shape, step advice, wrap-stage
-- | data. The instances recurse over the slot list; the compile and
-- | prove flows are top-level functions dispatching through these
-- | methods.
-- |
-- | Every other parameter is fixed by `prevsSpec`, so a caller pins
-- | only that one.
class CompilableSpec
  :: Type
  -> Type
  -> Int
  -> Type
  -> Type
  -> Type
  -> Type
  -> Constraint
class
  CompilableSpec prevsSpec prevsCarrier mpv valCarrier carrier vkCarrier blueprints
  | prevsSpec -> prevsCarrier mpv valCarrier carrier vkCarrier blueprints
  where
  -- | The rule's compile-time shape data.
  -- |
  -- | `selfStepDomainLog2s` holds every branch's own step domain
  -- | log2, which is what a `Self` slot's source domains are; an
  -- | `External` slot ignores it and reads the imported rule's step
  -- | domain off its prover index. During the pre-pass, which only
  -- | counts gates, callers pass `roughDomainsLog2` in every
  -- | position.
  shapeCompileData
    :: forall @nd ndPred
     . Add 1 ndPred nd
    => Compare 0 nd LT
    => Reflectable nd Int
    => CompileConfig mpv
    -> Vector nd Int
    -> ShapeCompileData mpv nd blueprints

  -- | The step solver's advice, plus the `ShapeProveSideInfo` the
  -- | wrap stage needs, assembled slot by slot.
  mkStepAdvice
    :: forall inputVal inputVar
     . CircuitType StepField inputVal inputVar
    => CompileConfig mpv
    -> StepCompileResult
    -> WrapCompileResult
    -> inputVal
    -> prevsCarrier
    -> vkCarrier
    -> Effect
         { stepAdvice ::
             StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal mpv
               carrier
               valCarrier
               vkCarrier
         , challengePolynomialCommitments :: Vector mpv (AffinePoint StepField)
         , baseCaseWrapPublicInputs :: Vector mpv (Array WrapField)
         }

  -- | The rule's wrap-stage data, assembled slot by slot from the
  -- | prevs and the step-advice side info.
  shapeProveData
    :: CompileConfig mpv
    -> WrapCompileResult
    -> ShapeProveSideInfo mpv
    -> prevsCarrier
    -> vkCarrier
    -> ShapeProveData mpv

--------------------------------------------------------------------------------
-- CompilableSpec Unit (N=0, NRR-shape)
--------------------------------------------------------------------------------

instance CompilableSpec Unit Unit 0 Unit Unit Unit Unit where
  shapeCompileData cfg _ =
    { stepProveCtx:
        { srsData:
            { blindingH:
                coerce (ProofFFI.srsBlindingGenerator cfg.srs.pallasSrs :: AffinePoint StepField)
            , perSlotFopDomainLog2s: Vector.nil
            , perSlotFopZkRows: Vector.nil
            , perSlotVkBlueprints: unit
            }
        , dummySg: nrrDummyWrapSg cfg.srs.pallasSrs cfg.srs.vestaSrs
        , crs: cfg.srs.vestaSrs
        , debug: cfg.debug
        , proofCache: cfg.proofCache
        }
    , wrapDomainLog2: Dummy.wrapDomainLog2ForProofsVerified 0
    }
    where
    -- Nothing is verified at `mpv = 0`, so this is never read; it is
    -- there because `stepCompile` takes an sg_old padding constant.
    nrrDummyWrapSg pallasSrs vestaSrs =
      ( Dummy.computeDummySgValues
          (Dummy.baseCaseDummies { maxProofsVerified: 0 })
          pallasSrs
          vestaSrs
      ).ipa.wrap.sg

  mkStepAdvice cfg _ wrapCR appInput _ _ =
    let
      bcd = Dummy.baseCaseDummies { maxProofsVerified: 0 }
      dummyHash = mkDummyMsgWrapHash bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
    in
      pure
        -- With no prev slots the `stepDomainLog2` below is dead — the
        -- per-slot dummy that consumes it is replicated to an empty
        -- vector — so `0` is a sentinel and any value would do. The
        -- wrap VK is rewritten here because `buildStepAdvice`'s is a
        -- dummy.
        { stepAdvice:
            over StepAdvice
              ( \r -> r
                  { wrapVerifierIndex = extractWrapVKCommsAdvice wrapCR.verifierIndex
                  , messagesForNextWrapProofDummyHash = dummyHash
                  }
              )
              ( buildStepAdvice @Unit
                  { publicInput: appInput
                  , stepDomainLog2: 0
                  , prevAppStates: unit
                  , sideloadedVKs: unit
                  }
              )
        , challengePolynomialCommitments: Vector.nil
        , baseCaseWrapPublicInputs: Vector.nil
        }

  shapeProveData _ _ _ _ _ =
    { prevSgs: Vector.nil
    , prevStepChallenges: Vector.nil
    , msgWrapChallenges: Vector.nil
    , prevUnfinalizedProofs: Vector.nil
    , prevStepAccs: Vector.nil
    , prevEvals: Vector.nil
    , prevWrapDomainIndices: Vector.nil
    , kimchiPrevEntries: Vector.nil
    , slotsValue: []
    }

--------------------------------------------------------------------------------
-- CompilableSpec Slot (N ≥ 1, recursive)
--------------------------------------------------------------------------------

-- | Recursive instance covering every `Slot n stmt /\ rest` shape,
-- | and all three slot sources: which source a slot has is the
-- | runtime `SlotWrapKey` in `cfg.perSlotImportedVKs`, on which the
-- | two prove-time methods dispatch.
instance
  ( CompilableSpec rest restPrevsCarrier restMpv restValCarrier restCarrier restVkCarrier restScaffolds
  -- Both orderings: `restMpv 1 mpv` synthesizes `mpv` from `restMpv`;
  -- `1 restMpv mpv` is the form `Vector.uncons` needs to recover
  -- `restMpv` from `mpv`.
  , Add restMpv 1 mpv
  , Add 1 restMpv mpv
  , Add pad mpv PaddedLength
  , Reflectable n Int
  , Reflectable mpv Int
  , Reflectable pad Int
  , Add slotPad n PaddedLength
  , Reflectable slotPad Int
  , Compare mpv 3 LT
  , Compare 0 mpv LT
  , Compare n 3 LT
  , CircuitType StepField prevHeadInput prevHeadInputVar
  , CircuitType StepField prevHeadOutput prevHeadOutputVar
  , SlotStatementsCarrier rest restValCarrier
  ) =>
  CompilableSpec
    (Slot n (StatementIO prevHeadInput prevHeadOutput) /\ rest)
    ( PrevSlot prevHeadInput n (StatementIO prevHeadInput prevHeadOutput)
        /\ restPrevsCarrier
    )
    mpv
    (StatementIO prevHeadInput prevHeadOutput /\ restValCarrier)
    ( Step.PerProofWitness
        WrapVkChunks
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
        /\ restCarrier
    )
    -- What the prove call supplies for this slot's wrap VK.
    (SideloadBundle.SlotProveVk WrapVkChunks /\ restVkCarrier)
    -- The compile-time blueprint for this slot's wrap-VK source, one
    -- constructor per source, which `buildSlotVkSources` turns into a
    -- `SlotVkSource` at circuit-build time.
    (SlotVkBlueprint WrapVkChunks /\ restScaffolds)
  where
  shapeCompileData cfg selfStepDomainLog2s =
    consShapeCompileData cfg selfStepDomainLog2s headSlot
      (shapeCompileData @rest restCfg selfStepDomainLog2s)
    where
    { head: headSlotWrapKey, tail: restSlotVKs } = Vector.uncons cfg.perSlotImportedVKs
    restCfg = cfg { perSlotImportedVKs = restSlotVKs }

    -- This slot as runtime data; the derivations from it — wrap
    -- domain, source step domains, `zk_rows`, VK blueprint — live in
    -- `Pickles.Prove.Slot`.
    headSlot :: RuntimeSlot.Slot
    headSlot = runtimeSlotOf (reflectType (Proxy @n)) headSlotWrapKey

  mkStepAdvice cfg stepCR wrapCR appInput (headSlot /\ restPrevs) (headVk /\ restVkCarrier) =
    consMkStepAdvice @n cfg.srs appInput slotParams headVk headSlot
      (mkStepAdvice @rest restCfg stepCR wrapCR appInput restPrevs restVkCarrier)
    where
    { head: headSlotWrapKey, tail: restSlotVKs } = Vector.uncons cfg.perSlotImportedVKs
    restCfg = cfg { perSlotImportedVKs = restSlotVKs }

    -- The same record `shapeCompileData` builds, so the derivations
    -- below read it through `Pickles.Prove.Slot` instead of deciding
    -- the slot's source once per value.
    runtimeSlot :: RuntimeSlot.Slot
    runtimeSlot = runtimeSlotOf (reflectType (Proxy @n)) headSlotWrapKey

    -- A side-loaded slot's wrap VK is a runtime witness, so its
    -- domains come off the bundle rather than off anything this
    -- compile knows. The witness is still sized at the slot's
    -- compile-time bound `n`; a smaller `actualWrapDomainSize` is
    -- masked in-circuit.
    slotParams = case headSlotWrapKey of
      SideLoadedKey ->
        { slotWrapVK: SideloadBundle.verifierIndex bundle
        , slotWrapDomainLog2: bundleWrapDomainLog2 bundle
        , slotStepDomainLog2:
            -- A side-loaded VK does not carry the prev's step domain;
            -- the step circuit dispatches over `[0..16]` in
            -- `Pickles.Step.FinalizeOtherProof`'s `SideLoadedMode`.
            -- This stand-in reaches only the `BasePrev` site, where
            -- `proofMustVerify` is `false`; `InductivePrev` reads the
            -- prev's own `stepDomainLog2`.
            Dummy.wrapDomainLog2ForProofsVerified (reflectType (Proxy @n))
        -- A side-loaded proof is always single-chunk: the side-loaded
        -- domain dispatch varies the domain log2, not the chunk count.
        , slotStepZkRows: zkRowsForNumChunks 1
        , slotWrapZkRows: zkRowsForNumChunks 1
        }
        where
        bundle = SideloadBundle.requireBundle headVk
      -- The key decides the slot's source, so a runtime VK supplied
      -- here would be silently dropped. Refuse instead: the caller
      -- believes this slot is side-loaded and it is not, and nothing
      -- downstream would tell them.
      _ | SideloadBundle.SideLoadedVk _ <- headVk -> unsafeThrow
        "mkStepAdvice: this slot's key is Self or External, so its wrap \
        \verification key is baked in at compile time, but a side-loaded \
        \verification key was supplied for it in `sideloadedVKs`"
      _ ->
        { slotWrapVK:
            RuntimeSlot.slotWrapVerifierIndex wrapCR.verifierIndex runtimeSlot
        , slotWrapDomainLog2:
            RuntimeSlot.slotWrapDomainLog2 cfg.selfWrapDomainLog2 runtimeSlot
        , slotStepDomainLog2:
            RuntimeSlot.slotStepDomainLog2
              (ProofFFI.proverIndexDomainLog2 stepCR.proverIndex)
              runtimeSlot
        -- A `Self` slot's prev step circuit is this rule, so its chunk
        -- count is the declared `@stepChunks`; `External` reads the
        -- imported rule's. A wrap circuit is always single-chunk.
        , slotStepZkRows:
            zkRowsForNumChunks (RuntimeSlot.slotNumChunks cfg.stepNumChunks runtimeSlot)
        , slotWrapZkRows: zkRowsForNumChunks 1
        }

  shapeProveData cfg wrapCR sideInfo (headSlot /\ restPrevs) (headVk /\ restVkCarrier) =
    consShapeProveData cfg.srs slotParams sideInfo headSlot
      (shapeProveData @rest restCfg wrapCR restSideInfo restPrevs restVkCarrier)
    where
    { head: headSlotWrapKey, tail: restSlotVKs } = Vector.uncons cfg.perSlotImportedVKs
    restCfg = cfg { perSlotImportedVKs = restSlotVKs }

    -- A `Self` slot verifies a proof of this same system, so it reads
    -- this compile's own wrap VK and domain; an `External` slot reads
    -- the imported compile's, which that compile stored; a side-loaded
    -- slot reads both off the runtime bundle.
    slotParams =
      { slotWrapVK: case headSlotWrapKey of
          Self -> wrapCR.verifierIndex
          External vks -> vks.wrapCompileResult.verifierIndex
          SideLoadedKey -> SideloadBundle.verifierIndex (SideloadBundle.requireBundle headVk)
      , slotWrapDomainLog2: case headSlotWrapKey of
          External vks -> vks.wrapDomainLog2
          SideLoadedKey -> bundleWrapDomainLog2 (SideloadBundle.requireBundle headVk)
          Self -> cfg.selfWrapDomainLog2
      , slotWidth: reflectType (Proxy @n)
      , slotPad: reflectType (Proxy @slotPad)
      }

    restSideInfo =
      { challengePolynomialCommitments:
          (Vector.uncons sideInfo.challengePolynomialCommitments).tail
      , unfinalizedSlots: (Vector.uncons sideInfo.unfinalizedSlots).tail
      , baseCaseWrapPublicInputs:
          (Vector.uncons sideInfo.baseCaseWrapPublicInputs).tail
      }

--------------------------------------------------------------------------------
-- Type-level rules spec
--
-- The same idea as `Pickles.Step.Slots.PrevsSpec` one level up: a list
-- over the branches rather than over one branch's prev slots. Each
-- `RulesCons` carries the three facts that vary per branch — that
-- branch's `mpv`, its prev statement types, and its prevs spec.
--
-- `inputVal`, `outputVal` and `prevInputVal` are not among them: they
-- parameterize the shared wrap VK's public-input layout, so they live
-- at the multi-branch level.
--------------------------------------------------------------------------------

-- | Kind: a type-level list of rule specs.
data RulesSpec

-- | The empty rules list, which terminates the instance recursion.
-- | `compileMulti` itself rejects it, through `Compare 0 branches LT`.
foreign import data RulesNil :: RulesSpec

-- | One branch's contribution to the rules list: its `mpv`, its prev
-- | statement types, its prevs spec, and the rest of the list.
foreign import data RulesCons :: Int -> Type -> Type -> RulesSpec -> RulesSpec

-- | A rule's per-slot `max_proofs_verified`, in slot order, read back
-- | as values from the `n` of each `Slot n stmt`, so the wrap
-- | circuit's slot widths are derived from the spec rather than
-- | restated beside it.
class SlotWidths (prevsSpec :: Type) where
  slotWidthsOf :: forall proxy. proxy prevsSpec -> Array Int

instance SlotWidths Unit where
  slotWidthsOf _ = []

instance (Reflectable n Int, SlotWidths rest) => SlotWidths (Slot n stmt /\ rest) where
  slotWidthsOf _ = Array.cons (reflectType (Proxy @n)) (slotWidthsOf (Proxy @rest))

-- | The wrap circuit's per-slot widths, overlaid from every branch's own
-- | slot list.
-- |
-- | A branch with `mpv` slots occupies the last `mpv` positions of
-- | the wrap circuit's `mpvMax`, so two branches can reach the same
-- | position and must agree on its width there. `mpvMax` is a maximum
-- | over branches, so every position is covered and the result is
-- | total.
deriveWrapSlotWidths :: Int -> Array (Array Int) -> Array Int
deriveWrapSlotWidths mpvMax perRule =
  Array.mapWithIndex (\i _ -> atPosition i) (Array.replicate mpvMax unit)
  where
  atPosition i = case Array.nub (Array.mapMaybe (widthAt i) perRule) of
    [ w ] -> w
    [] -> unsafeThrow
      $ "compileMulti: no rule declares slot " <> show i <> " of " <> show mpvMax
    ws -> unsafeThrow
      $ "compileMulti: rules disagree on the width of slot "
          <> show i
          <> ": "
          <> show ws
          <> ". A slot's width is its `Slot n _ _`, and every rule whose "
          <> "prevs reach that slot must declare the same n."

  widthAt i ws =
    let
      pad = mpvMax - Array.length ws
    in
      if i < pad then Nothing else Array.index ws (i - pad)

-- | Type-level `max` over two `Int` kinds, dispatched via `Compare`.
class IntMax (a :: Int) (b :: Int) (c :: Int) | a b -> c

class IntMaxOrd :: PrimOrdering.Ordering -> Int -> Int -> Int -> Constraint
class IntMaxOrd ord a b c | ord a b -> c

instance IntMaxOrd LT a b b
instance IntMaxOrd EQ a b a
instance IntMaxOrd GT a b a

instance (Compare a b ord, IntMaxOrd ord a b c) => IntMax a b c

-- | `mpvMax` is the maximum `ruleMpv` over `rules`, as an equality
-- | rather than a bound. `CompilableRulesSpecShape`'s per-rule
-- | `Add mpvPad ruleMpv mpvMax` already gives `ruleMpv ≤ mpvMax`;
-- | this pins `mpvMax` itself, so two call sites deriving it from the
-- | same `rules` cannot disagree.
class MaxOfRulesMpvs (rules :: RulesSpec) (mpvMax :: Int) | rules -> mpvMax

instance MaxOfRulesMpvs RulesNil 0

instance
  ( MaxOfRulesMpvs rest restMax
  , IntMax ruleMpv restMax mpvMax
  ) =>
  MaxOfRulesMpvs (RulesCons ruleMpv valCarrier prevsSpec rest) mpvMax

-- | What `compileMulti` needs that is shared across all branches. The
-- | per-branch data travels alongside, in the `rulesCarrier`.
type CompileMultiConfig =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , debug :: Boolean
  , wrapDomainOverride :: Maybe Int
  -- | Optional disk proof-cache (test/dev). `Nothing` = no caching.
  , proofCache :: Maybe ProofCache
  -- | Optional on-disk Lagrange-basis cache. When `Just`, compile
  -- | warms each of the program's real domains through it before any
  -- | constraint building, so each basis is FFT'd once ever and
  -- | injected from disk thereafter. `Nothing` leaves kimchi to
  -- | compute bases lazily in-process, unpersisted.
  , lagrangeCache :: Maybe LagrangeCache
  }

-- | The prover for one branch: one `RulesCons` of the rules spec
-- | yields one of these, at that branch's shape.
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> Type -> Row (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier vkCarrier inputVal outputVal r =
  BranchProver
    ( AdviceHandler r
      -> StepInputs prevsSpec inputVal prevsCarrier vkCarrier
      -> Effect (Either ProveError (CompiledProof mpv (StatementIO inputVal outputVal)))
    )

-- | A multi-branch compile's verification keys: one `wrap` VK, under
-- | which every branch's wrap proof verifies — the wrap statement's
-- | `whichBranch` says which step circuit was wrapped — and one
-- | `StepCompileResult` per branch, which are not shared.
type MultiVKs perBranchStepCarrier =
  { wrap :: WrapCompileResult
  , perBranchStep :: perBranchStepCarrier
  , wrapDomainLog2 :: Int
  -- | The compile's declared `@stepChunks`, propagated so that a
  -- | consumer building `ProverVKs` for an `External` slot reads it
  -- | directly rather than back-deriving it from the step circuit's
  -- | realized domain log2.
  , stepChunks :: Int
  }

-- | What `compileMulti` returns: one prover per branch, and one
-- | shared `tag`, `verifier` and set of VKs.
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
  , tag :: Tag (StatementIO inputVal outputVal) mpvMax
  , verifier :: Verifier
  , vks :: MultiVKs perBranchStepCarrier
  -- | Per-branch `ProverVKs` handles, for a caller that wants to
  -- | reference one branch from another proof system via `External`.
  , perBranchVKs :: perBranchVKsCarrier
  }

--------------------------------------------------------------------------------
-- CompilableRulesSpec
--
-- Dispatch over the branches, one instance per rule. The rules are
-- reached through class methods rather than stored in the carrier
-- because PS rejects a record field holding `StepRule`'s rank-2
-- forall: each instance is monomorphic, so a rule value is used
-- inside a method body without ever being stored as a record value.
--------------------------------------------------------------------------------

-- | The branch-level counterpart of `CompilableSpec`: one instance
-- | per rule, walking the rules spec.
-- |
-- | Two branch counts appear. `topBranches` is the whole compile's
-- | count and stays fixed through the recursion; `branches` is the
-- | count of the tail still to be walked. `RuleEntry`'s `nd` binds to
-- | `topBranches`, so every rule's step functions see a
-- | `StepProveContext mpv topBranches` — a context whose multi-domain
-- | dispatch ranges over every branch's step domain, not just the
-- | tail's.
class CompilableRulesSpec
  :: RulesSpec
  -> Type
  -> Type
  -> Type
  -> Int
  -> Int
  -> Int
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
  -> Row (Type -> Type)
  -> Constraint
class
  CompilableRulesSpec
    rs
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
    r
  | rs topBranches r ->
    branches mpvMax rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
  where
  -- | The number of branches, counted by walking `rs`.
  branchCount :: forall proxy. proxy rs -> Int

  -- | Each branch's own slot widths, in branch order, which
  -- | `deriveWrapSlotWidths` overlays into the wrap circuit's single
  -- | `mpvMax`-long list.
  ruleSlotWidths :: forall proxy. proxy rs -> Array (Array Int)

  -- | Each `RuleEntry`'s `stepCompileFn`, in branch order. The chain
  -- | is heterogeneous: branch `i`'s thunk takes a context at that
  -- | branch's own `mpv`.
  extractStepCompileFns :: rulesCarrier -> stepCompileFnsCarrier

  -- | Every branch's step compile, run against the matching context,
  -- | in branch order.
  runStepCompiles
    :: AdviceHandler r
    -> perBranchCtxsCarrier
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | Each `RuleEntry`'s `stepProveFn`, in branch order, which
  -- | `buildBranchProvers` composes with the shared wrap flow.
  extractStepProveFns :: rulesCarrier -> stepProveFnsCarrier

  -- | The per-branch step results, in the shape
  -- | `buildWrapMainConfigMulti` takes: each branch's `mpv`, its step
  -- | domain log2 and its step VK.
  buildWrapPerBranchVec
    :: perBranchStepCompileResults
    -> Vector branches
         { mpv :: Int
         , stepDomainLog2 :: Int
         , stepVK :: VerifierIndex VestaG StepField
         }

instance
  CompilableRulesSpec RulesNil
    inputVal
    outputVal
    prevInputVal
    topBranches
    0
    mpvMax
    Unit
    Unit
    Unit
    Unit
    Unit
    r
  where
  branchCount _ = 0
  ruleSlotWidths _ = []
  extractStepCompileFns _ = unit
  runStepCompiles _ _ _ = pure unit
  extractStepProveFns _ = unit
  buildWrapPerBranchVec _ = Vector.nil

instance
  ( CompilableRulesSpec rest inputVal outputVal prevInputVal
      topBranches
      restBranches
      mpvMax
      restCarrier
      restStepCompileFns
      restCtxs
      restStepCompileResults
      restStepProveFns
      r
  , Add restBranches 1 branches
  , SlotWidths prevsSpec
  , StepSlotsCarrier
      prevsSpec
      WrapVkChunks
      StepIPARounds
      WrapIPARounds
      (F StepField)
      (Type2 (SplitField (F StepField) Boolean))
      Boolean
      ruleMpv
      carrier
      vkSourcesCarrier
  -- `outputSize` derives from `mpvMax`, not from the rule's own
  -- `mpv`: the step public input is `mpvMax`-shaped.
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , Reflectable ruleMpv Int
  -- The runtime side-loaded VK carrier, bound once here so that the
  -- `RuleEntry` and the `StepAdvice` its closure takes share it.
  , SideloadedVKsCarrier prevsSpec vkCarrier
  ) =>
  CompilableRulesSpec
    (RulesCons ruleMpv valCarrier prevsSpec rest)
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize vkCarrier blueprints r
        /\ restCarrier
    )
    ( ( AdviceHandler r
        -> PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> Effect PProveStep.StepCompileResult
      )
        /\ restStepCompileFns
    )
    (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
    (PProveStep.StepCompileResult /\ restStepCompileResults)
    ( ( AdviceHandler r
        -> PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> PProveStep.StepCompileResult
        -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
             inputVal
             ruleMpv
             carrier
             valCarrier
             vkCarrier
        -> Effect
             (Either EvaluationError (PProveStep.StepProveResult outputSize))
      )
        /\ restStepProveFns
    )
    r
  where
  branchCount _ =
    1 + branchCount
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @r
      (Proxy :: Proxy rest)
  ruleSlotWidths _ =
    Array.cons (slotWidthsOf (Proxy :: Proxy prevsSpec))
      ( ruleSlotWidths
          @rest
          @inputVal
          @outputVal
          @prevInputVal
          @topBranches
          @restBranches
          @mpvMax
          @restCarrier
          @restStepCompileFns
          @restCtxs
          @restStepCompileResults
          @restStepProveFns
          @r
          (Proxy :: Proxy rest)
      )
  extractStepCompileFns (RuleEntry r /\ rest) =
    r.stepCompileFn
      /\ extractStepCompileFns
        @rest
        @inputVal
        @outputVal
        @prevInputVal
        @topBranches
        @restBranches
        @mpvMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
        @r
        rest
  runStepCompiles handler (ctx /\ restCtxs) (RuleEntry r /\ restEntries) = do
    headResult <- r.stepCompileFn handler ctx
    tailResults <- runStepCompiles
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @r
      handler
      restCtxs
      restEntries
    pure (headResult /\ tailResults)
  buildWrapPerBranchVec (headResult /\ restResults) =
    let
      headRecord =
        { mpv: reflectType (Proxy :: Proxy ruleMpv)
        , stepDomainLog2: proverIndexDomainLog2 headResult.proverIndex
        , stepVK: headResult.verifierIndex
        }
      restVec = buildWrapPerBranchVec
        @rest
        @inputVal
        @outputVal
        @prevInputVal
        @topBranches
        @restBranches
        @mpvMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
        @r
        restResults
    in
      headRecord :< restVec
  extractStepProveFns (RuleEntry r /\ rest) =
    r.stepProveFn
      /\ extractStepProveFns
        @rest
        @inputVal
        @outputVal
        @prevInputVal
        @topBranches
        @restBranches
        @mpvMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
        @r
        rest

--------------------------------------------------------------------------------
-- CompilableRulesSpecShape — shape-data methods.
--
-- Separate from `CompilableRulesSpec` because that class must not
-- carry a `CompilableSpec` super-constraint: PS cannot always
-- discharge one at a call site, and the failure cascades through the
-- funDep chain and leaves every class parameter unresolved. Split,
-- the structural methods stay light and only callers of the
-- shape-data methods take on the heavier discharge.
--------------------------------------------------------------------------------

class
  CompilableRulesSpec rs inputVal outputVal prevInputVal topBranches branches mpvMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
    r <=
  CompilableRulesSpecShape
    rs
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
    proversCarrier
    r
  | rs topBranches r -> branches mpvMax rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
    perBranchStepCompileResults stepProveFnsCarrier
    proversCarrier
  where
  -- | Every branch's own step domain log2, in branch order, each
  -- | obtained by building that rule's constraint system against a
  -- | placeholder context and counting its gates. Callers pass
  -- | `roughDomainsLog2` in every position of the placeholder.
  prePassDomainLog2s
    :: AdviceHandler r
    -> CompileMultiConfig
    -> Int
    -- ^ the declared `@stepChunks`
    -> Vector topBranches Int
    -> rulesCarrier
    -> Effect (Vector branches Int)

  -- | Every branch's step compile, each run against a context built
  -- | from the same full vector of step domain log2s.
  runMultiCompile
    :: AdviceHandler r
    -> CompileMultiConfig
    -> Int
    -- ^ the declared `@stepChunks`
    -> Vector topBranches Int
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | One `BranchProver` per branch: a closure that runs that
  -- | branch's step solve and prove, then the shared wrap solve and
  -- | prove with `whichBranch` set to its own index. The index
  -- | argument is the head entry's; top-level callers pass `0`.
  buildBranchProvers
    :: forall stepChunks numChunksPred vecLen vecLenPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 totalBasesMax totalBasesMaxPred
     . Reflectable vecLen Int
    => Add 1 vecLenPred vecLen
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
    => Add mpvMax nonSgBases totalBasesMax
    => Add 1 totalBasesMaxPred totalBasesMax
    => Proxy stepChunks
    -> Int
    -> CompileMultiConfig
    -> WrapCompileResult
    -> Vector vecLen
         { mpv :: Int
         , stepDomainLog2 :: Int
         , stepVK :: VerifierIndex VestaG StepField
         }
    -> Vector topBranches Int
    -> perBranchStepCompileResults
    -> rulesCarrier
    -> Effect proversCarrier

-- | The per-branch step compiles, and the step domain log2s the
-- | pre-pass found for them. Instantiating both class parameters at
-- | `topBranches` is what makes this the recursion's outermost call.
runMultiCompileFull
  :: forall @rs @inputVal @outputVal @prevInputVal @topBranches @mpvMax @r
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal
       topBranches
       topBranches
       mpvMax
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
       r
  => Reflectable topBranches Int
  => AdviceHandler r
  -> CompileMultiConfig
  -> Int
  -- ^ the declared `@stepChunks`
  -> rulesCarrier
  -> Effect
       { stepResults :: perBranchStepCompileResults
       , log2s :: Vector topBranches Int
       }
runMultiCompileFull handler cfg stepNumChunks rules = do
  let
    placeholder = Vector.replicate roughDomainsLog2
  log2s <- prePassDomainLog2s
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @topBranches
    @topBranches
    @mpvMax
    @rulesCarrier
    @stepCompileFnsCarrier
    @perBranchCtxsCarrier
    @perBranchStepCompileResults
    @stepProveFnsCarrier
    @proversCarrier
    @r
    handler
    cfg
    stepNumChunks
    placeholder
    rules
  -- Warming happens here because the pre-pass has just yielded the
  -- real per-branch step domains and no constraint building — which
  -- is what fires the lazy `mkConstLagrangeBaseLookup` reads — has
  -- started. The warmed `CRS` is shared by reference into prove, so
  -- the prover finds every basis already present.
  --
  -- Vesta is warmed at the program's real step domains; pallas at all
  -- of `[13, 14, 15]`, which is every wrap domain there is, so no
  -- slot needs inspecting to know a `Self`, `External` or side-loaded
  -- slot's domain is covered. The cost is three small bases.
  for_ cfg.lagrangeCache \cache -> do
    warmVesta <- warmer cache vestaOps cfg.srs.vestaSrs
    for_ log2s warmVesta
    warmPallas <- warmer cache pallasOps cfg.srs.pallasSrs
    for_ [ 13, 14, 15 ] warmPallas
  stepResults <- runMultiCompile
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @topBranches
    @topBranches
    @mpvMax
    @rulesCarrier
    @stepCompileFnsCarrier
    @perBranchCtxsCarrier
    @perBranchStepCompileResults
    @stepProveFnsCarrier
    @proversCarrier
    @r
    handler
    cfg
    stepNumChunks
    log2s
    rules
  pure { stepResults, log2s }

instance
  CompilableRulesSpecShape RulesNil
    inputVal
    outputVal
    prevInputVal
    topBranches
    0
    mpvMax
    Unit
    Unit
    Unit
    Unit
    Unit
    Unit
    r
  where
  prePassDomainLog2s _ _ _ _ _ = pure Vector.nil
  runMultiCompile _ _ _ _ _ = pure unit
  buildBranchProvers _ _ _ _ _ _ _ _ = pure unit

instance
  ( CompilableRulesSpecShape rest inputVal outputVal prevInputVal
      topBranches
      restBranches
      mpvMax
      restCarrier
      restStepCompileFns
      restCtxs
      restStepCompileResults
      restStepProveFns
      restProvers
      r
  , CompilableSpec prevsSpec prevsCarrier ruleMpv valCarrier
      carrier
      vkCarrier
      blueprints
  , SlotStatementsCarrier prevsSpec valCarrier
  -- Per-rule step+wrap constraints needed by runMultiProverBody.
  , CircuitGateConstructor StepField VestaG
  , CircuitGateConstructor WrapField PallasG
  , Reflectable ruleMpv Int
  , Reflectable pad Int
  , Reflectable outputSize Int
  , Add pad ruleMpv PaddedLength
  -- `outputSize` derives from `mpvMax`, the wrap circuit's max.
  , Reflectable mpvPad Int
  , Add mpvPad ruleMpv mpvMax
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  -- Wrap-stage constraints at `mpvMax`, the shape
  -- `padShapeProveData` widens the per-rule `ruleMpv` shape to.
  , Reflectable mpvMax Int
  , Reflectable padMax Int
  , Add padMax mpvMax PaddedLength
  , Compare mpvMax 3 LT
  -- `topBranches` stays fixed across the recursion, and
  -- `buildStepProveCtx` and the `Vector` dispatch need it.
  , Reflectable topBranches Int
  , Compare 0 topBranches LT
  , Add 1 topBranchesPred topBranches
  , CircuitType StepField inputVal inputVar
  , CircuitType StepField outputVal outputVar
  , CircuitType StepField prevInputVal prevInputVar
  , StepSlotsTyp prevsSpec carrier carrierFVar
  , CheckedType StepField (KimchiConstraint StepField) inputVar
  , CompilableRulesSpec
      (RulesCons ruleMpv valCarrier prevsSpec rest)
      inputVal
      outputVal
      prevInputVal
      topBranches
      branches
      mpvMax
      ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize vkCarrier blueprints r
          /\ restCarrier
      )
      ( ( AdviceHandler r
          -> PProveStep.StepProveContext ruleMpv topBranches blueprints
          -> Effect PProveStep.StepCompileResult
        )
          /\ restStepCompileFns
      )
      (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
      (PProveStep.StepCompileResult /\ restStepCompileResults)
      ( ( AdviceHandler r
          -> PProveStep.StepProveContext ruleMpv topBranches blueprints
          -> PProveStep.StepCompileResult
          -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
               inputVal
               ruleMpv
               carrier
               valCarrier
               vkCarrier
          -> Effect
               (Either EvaluationError (PProveStep.StepProveResult outputSize))
        )
          /\ restStepProveFns
      )
      r
  , Add 1 restBranches branches
  -- `(:<)` needs `Add restBranches 1 branches`; PS does not commute
  -- `Add`, so both orderings are stated.
  , Add restBranches 1 branches
  ) =>
  CompilableRulesSpecShape
    (RulesCons ruleMpv valCarrier prevsSpec rest)
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize vkCarrier blueprints r
        /\ restCarrier
    )
    ( ( AdviceHandler r
        -> PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> Effect PProveStep.StepCompileResult
      )
        /\ restStepCompileFns
    )
    (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
    (PProveStep.StepCompileResult /\ restStepCompileResults)
    ( ( AdviceHandler r
        -> PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> PProveStep.StepCompileResult
        -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
             inputVal
             ruleMpv
             carrier
             valCarrier
             vkCarrier
        -> Effect
             (Either EvaluationError (PProveStep.StepProveResult outputSize))
      )
        /\ restStepProveFns
    )
    -- `BranchProver`'s `mpv` is `mpvMax`, not `ruleMpv`: every
    -- branch's `CompiledProof` presents the wrap-level width, with
    -- its own width hidden inside `widthData`. `BranchProver` is a
    -- newtype rather than an alias so that the instance head shows PS
    -- a saturated type constructor instead of a function type.
    ( BranchProver prevsSpec mpvMax prevsCarrier vkCarrier inputVal outputVal r
        /\ restProvers
    )
    r
  where
  prePassDomainLog2s handler cfg stepNumChunks placeholder (RuleEntry r /\ restEntries) = do
    let
      placeholderCtx = buildStepProveCtx @prevsSpec cfg stepNumChunks
        (reflectType (Proxy :: Proxy mpvMax))
        r.slotVKs
        placeholder
    headLog2 <- r.preComputeStepDomainLog2Fn handler placeholderCtx
    restVec <- prePassDomainLog2s
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
      @r
      handler
      cfg
      stepNumChunks
      placeholder
      restEntries
    pure (headLog2 :< restVec)
  runMultiCompile handler cfg stepNumChunks log2s (RuleEntry r /\ restEntries) = do
    let
      ctx = buildStepProveCtx @prevsSpec cfg stepNumChunks
        (reflectType (Proxy :: Proxy mpvMax))
        r.slotVKs
        log2s
    headResult <- r.stepCompileFn handler ctx
    tailResults <- runMultiCompile
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
      @r
      handler
      cfg
      stepNumChunks
      log2s
      restEntries
    pure (headResult /\ tailResults)
  buildBranchProvers
    ncProxy
    branchIdx
    cfg
    wrapResult
    perBranchVec
    allStepDomainLog2s
    (headStepCR /\ restStepResults)
    (headEntry /\ restEntries) = do
    let
      thisBranch = branchIdx
      -- `branchIdx` is the recursion depth, so it indexes this
      -- branch's own entry of the full step-domain vector.
      headLog2 =
        Vector.index allStepDomainLog2s (unsafeFinite @topBranches branchIdx)
      headProver = BranchProver \handler stepInputs ->
        runMultiProverBody
          @prevsSpec
          @ruleMpv
          @valCarrier
          @carrier
          @inputVal
          @inputVar
          @outputVal
          @outputVar
          @prevInputVal
          @prevInputVar
          @topBranches
          @mpvMax
          @mpvPad
          handler
          ncProxy
          thisBranch
          cfg
          wrapResult
          perBranchVec
          allStepDomainLog2s
          headStepCR
          headLog2
          headEntry
          stepInputs
    restProvers <- buildBranchProvers
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
      @r
      ncProxy
      (branchIdx + 1)
      cfg
      wrapResult
      perBranchVec
      allStepDomainLog2s
      restStepResults
      restEntries
    pure (headProver /\ restProvers)

--------------------------------------------------------------------------------
-- RuleEntry / mkRuleEntry — per-rule entry in the multi-branch carrier.
--------------------------------------------------------------------------------

-- | One branch, as the rules carrier stores it: monomorphic closures
-- | over the rank-2 `StepRule` captured at `mkRuleEntry` time, since
-- | PS rejects a record field holding the rule itself.
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
  -> Row (Type -> Type)
  -> Type
data RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize vkCarrier blueprints r = RuleEntry
  { -- | Given a placeholder context, this rule's own step domain
    -- | log2, counted from a one-shot constraint-system build.
    --
    -- | `nd` is the compile's branch count, over which
    -- | `finalizeOtherProofCircuit` dispatches for `Self` prev slots.
    preComputeStepDomainLog2Fn ::
      AdviceHandler r -> PProveStep.StepProveContext mpv nd blueprints -> Effect Int
  , stepCompileFn ::
      AdviceHandler r -> PProveStep.StepProveContext mpv nd blueprints -> Effect PProveStep.StepCompileResult
  -- | `vkCarrier` is a `RuleEntry` parameter rather than a forall in
  -- | this field, so that the closure body's `stepSolveAndProve` sees
  -- | a saturated `StepAdvice`.
  , stepProveFn ::
      AdviceHandler r
      -> PProveStep.StepProveContext mpv nd blueprints
      -> PProveStep.StepCompileResult
      -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
           inputVal
           mpv
           carrier
           valCarrier
           vkCarrier
      -> Effect (Either EvaluationError (PProveStep.StepProveResult outputSize))
  -- | Where each slot's wrap VK comes from, in slot order.
  , slotVKs :: Vector mpv SlotWrapKey
  }

-- | A `RuleEntry` whose closures capture the given rule and invoke it
-- | through `preComputeStepDomainLog2`, `stepCompile` and
-- | `stepSolveAndProve`.
mkRuleEntry
  :: forall @mpvMax @outputVal @prevInputVal @r
       prevsSpec mpv mpvPad nd ndPred outputSize valCarrier
       inputVal inputVar outputVar prevInputVar
       carrier carrierVar pad unfsTotal digestPlusUnfs
       compileSideloadedVkCarrier sideloadedVkCarrier blueprints
       vkSourcesCarrier
   . CircuitGateConstructor StepField VestaG
  -- `prevsSpec` determines `vkSourcesCarrier`, so the compile- and
  -- prove-path constraints share one binder for it and differ only in
  -- their `cell`: a compile-time VK descriptor here, synthesised by
  -- `MkUnitVkCarrier`, and a runtime bundle below. A side-loaded VK
  -- is a wrap VK, hence `WrapVkChunks`.
  => BuildSlotVkSources (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean) prevsSpec WrapVkChunks mpv blueprints compileSideloadedVkCarrier vkSourcesCarrier
  => MkUnitVkCarrier prevsSpec compileSideloadedVkCarrier
  -- Prove path: the cells carry a bundle at exactly the side-loaded
  -- slots, taken from `StepAdvice.sideloadedVKs`.
  => BuildSlotVkSources (SideloadBundle.SlotProveVk WrapVkChunks) prevsSpec WrapVkChunks mpv blueprints sideloadedVkCarrier vkSourcesCarrier
  => SideloadedVKsCarrier prevsSpec sideloadedVkCarrier
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Add mpvPad mpv mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
       vkSourcesCarrier
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => SlotStatementsCarrier prevsSpec valCarrier
  => PStepRule r mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -- | Where each slot's wrap VK comes from, in slot order.
  -> Vector mpv SlotWrapKey
  -> Effect (RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize sideloadedVkCarrier blueprints r)
mkRuleEntry rule slotVKs =
  pure $ RuleEntry
    { preComputeStepDomainLog2Fn: \handler ctx ->
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
          @nd
          handler
          ctx
          rule
    , stepCompileFn: \handler ctx ->
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
          @nd
          handler
          ctx
          rule
    , stepProveFn: \handler ctx compileResult advice ->
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
          @nd
          handler
          ctx
          rule
          compileResult
          advice
    , slotVKs
    }

-- A local name for `StepRuleAt`, to keep the `RuleEntry` field types
-- free of an import cycle.
type PStepRule r mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar =
  PProveStep.StepRuleAt r mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar

--------------------------------------------------------------------------------
-- compileMulti — N-branch compile entry point.
--
-- Three stages: each branch's step circuit is compiled on its own, at
-- its own prevs spec and `max_proofs_verified`; one wrap circuit is
-- compiled over all of them; and each branch gets a prover closure
-- that bakes its own index into the wrap statement's `whichBranch`.
--
-- `inputVal`, `outputVal` and `prevInputVal` are shared across the
-- branches, because the wrap VK's public-input layout is the same for
-- every proof under it.
--------------------------------------------------------------------------------

-- | One rule's `StepProveContext`: the shared config combined with
-- | that rule's `slotVKs` and run through `shapeCompileData` for the
-- | per-slot layout.
buildStepProveCtx
  :: forall @prevsSpec @nd ndPred prevsCarrier mpv valCarrier carrier vkCarrier blueprints
   . CompilableSpec prevsSpec prevsCarrier mpv valCarrier carrier vkCarrier blueprints
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => CompileMultiConfig
  -> Int
  -- ^ the declared `@stepChunks`
  -> Int
  -- ^ the compile's `mpvMax`, which fixes its wrap domain
  -> Vector mpv SlotWrapKey
  -> Vector nd Int
  -> PProveStep.StepProveContext mpv nd blueprints
buildStepProveCtx cfg stepNumChunks selfMpvMax slotVKs selfStepDomainLog2s =
  let
    perRuleCfg =
      { srs: cfg.srs
      , perSlotImportedVKs: slotVKs
      , debug: cfg.debug
      , stepNumChunks
      , proofCache: cfg.proofCache
      , selfWrapDomainLog2:
          resolveSelfWrapDomainLog2 selfMpvMax cfg.wrapDomainOverride
      }
    shape = shapeCompileData @prevsSpec perRuleCfg selfStepDomainLog2s
  in
    shape.stepProveCtx

--------------------------------------------------------------------------------
-- runMultiProverBody — per-branch prover body.
--
-- Step advice, then wrap-stage data, then the step proof, then the
-- deferred values the wrap circuit checks, then the wrap proof, then
-- the `CompiledProof` the two are packaged into.
--
-- A top-level function rather than a class method, so its per-rule
-- type variables and constraints stay here instead of landing on the
-- class instance head. `buildBranchProvers` calls it from each
-- branch's closure with that branch's index and step result.
--------------------------------------------------------------------------------

runMultiProverBody
  :: forall @prevsSpec prevsCarrier @mpv @valCarrier @carrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
       @topBranches
       @mpvMax @mpvPad @stepChunks numChunksPred
       branches branchesPred topBranchesPred
       pad unfsTotal digestPlusUnfs outputSize carrierFVar
       padMax totalBasesMax totalBasesMaxPred
       tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
       vkCarrier blueprints r
   . CompilableSpec prevsSpec prevsCarrier mpv valCarrier carrier vkCarrier blueprints
  => SlotStatementsCarrier prevsSpec valCarrier
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Add 1 branchesPred branches
  -- `topBranches` is the count threaded through `RuleEntry`'s `nd`
  -- and the multi-domain vector `finalizeOtherProofCircuit` reads;
  -- `branches` is the wrap circuit's per-branch carrier count. They
  -- coincide, but stay separate to match the rule-level signatures.
  => Reflectable topBranches Int
  => Compare 0 topBranches LT
  => Add 1 topBranchesPred topBranches
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable mpvPad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Add mpvPad mpv mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  -- The constraints above are at the rule's own `mpv`; those below
  -- are at the wrap circuit's possibly wider `mpvMax`.
  => Reflectable mpvMax Int
  => Reflectable padMax Int
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
  => Add padMax mpvMax PaddedLength
  => Compare mpvMax 3 LT
  => Add mpvMax nonSgBases totalBasesMax
  => Add 1 totalBasesMaxPred totalBasesMax
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => StepSlotsTyp prevsSpec carrier carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => AdviceHandler r
  -> Proxy stepChunks
  -> Int
  -- ^ branchIdx — baked into the wrap statement's `whichBranch`.
  -> CompileMultiConfig
  -> WrapCompileResult
  -> Vector branches
       { mpv :: Int
       , stepDomainLog2 :: Int
       , stepVK :: VerifierIndex VestaG StepField
       }
  -- ^ the same per-branch vector wrap compile was given, from which
  --   the wrap solver rebuilds the same `WrapMainConfig`
  -> Vector topBranches Int
  -- ^ every branch's step domain log2, which gives this rule's
  --   `finalizeOtherProofCircuit` its dispatch table for `Self` slots
  -> PProveStep.StepCompileResult
  -- ^ this branch's step compile result
  -> Int
  -- ^ this branch's selfStepDomainLog2 (from the pre-pass)
  -> RuleEntry prevsSpec mpv topBranches valCarrier inputVal carrier outputSize vkCarrier blueprints r
  -> StepInputs prevsSpec inputVal prevsCarrier vkCarrier
  -> Effect (Either ProveError (CompiledProof mpvMax (StatementIO inputVal outputVal)))
runMultiProverBody
  handler
  ncProxy
  branchIdx
  cfg
  wrapResult
  perBranchVec
  allStepDomainLog2s
  stepCR
  selfStepDomainLog2
  (RuleEntry r)
  { appInput, prevs, sideloadedVKs } = do
  let
    perRuleCfg =
      { srs: cfg.srs
      , perSlotImportedVKs: r.slotVKs
      , debug: cfg.debug
      , stepNumChunks: reflectType ncProxy
      , proofCache: cfg.proofCache
      , selfWrapDomainLog2:
          resolveSelfWrapDomainLog2
            (reflectType (Proxy :: Proxy mpvMax))
            cfg.wrapDomainOverride
      }
    -- Every branch's step domain log2s, not just this branch's: that
    -- is the dispatch table `finalizeOtherProofCircuit` needs for
    -- `Self` slots.
    shape = shapeCompileData @prevsSpec perRuleCfg allStepDomainLog2s

  { stepAdvice, challengePolynomialCommitments, baseCaseWrapPublicInputs } <-
    mkStepAdvice @prevsSpec perRuleCfg stepCR wrapResult appInput
      prevs
      sideloadedVKs

  let
    PProveStep.StepAdvice sa = stepAdvice

    proveDataSideInfo =
      { challengePolynomialCommitments
      , unfinalizedSlots: sa.publicUnfinalizedProofs
      , baseCaseWrapPublicInputs
      }
    proveData = shapeProveData @prevsSpec perRuleCfg wrapResult
      proveDataSideInfo
      prevs
      sideloadedVKs

    outerMpvMax = reflectType (Proxy @mpvMax)
    -- `maxProofsVerified: 0`, not `mpvMax`: that is the
    -- `forceOrderFor` sequence which draws
    -- `unfinalizedConstantDummy` first, putting its four challenges
    -- on the random oracle's first four counters.
    bcdMax = baseCaseDummies { maxProofsVerified: 0 }
    dummySgsMax = computeDummySgValues bcdMax cfg.srs.pallasSrs cfg.srs.vestaSrs
    -- The two dummy sgs live on different curves: `prevSgs` and
    -- `prevStepAccs` take the Pallas one, `kimchiPrevEntries` the
    -- Vesta one.
    dummyStepSgInWrapField = dummySgsMax.ipa.step.sg -- AffinePoint WrapField
    dummyWrapSgInStepField = dummySgsMax.ipa.wrap.sg -- AffinePoint StepField

    -- `wrapDummyUnfinalizedProof`'s nested shape, flattened into the
    -- `PerProofUnfinalized` record `ShapeProveData` carries. Both
    -- sides are already wrap-field, so nothing crosses fields here.
    dummyUnfRaw = wrapDummyUnfinalizedProof bcdMax
    dummyUnfDv = dummyUnfRaw.deferredValues
    dummyPlonk = dummyUnfDv.plonk

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

    -- Every field of the dummy evaluations, `publicEvals` included,
    -- is a random-oracle draw rather than a zero placeholder.
    de = bcdMax.dummyEvals
    pe pe' = { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }

    dummyPrevEvalsMax = AllocEvals
      { ftEval1: F de.ftEval1
      , publicEvals: pe de.publicEvals
      , zEvals: pe de.zEvals
      , witnessEvals: map pe de.witnessEvals
      , coeffEvals: map pe de.coeffEvals
      , sigmaEvals: map pe de.sigmaEvals
      , indexEvals: map pe de.indexEvals
      }

    padDummies =
      { dummyPrevSg: dummyStepSgInWrapField
      , dummyPrevStepChals: dummyIpaChallenges.stepExpanded
      , dummyMsgWrapChal: dummyIpaChallenges.wrapExpanded
      , dummyPrevUnfinalizedProof: dummyPpu
      , dummyPrevStepAcc:
          WeierstrassAffinePoint
            { x: F (unwrap dummyStepSgInWrapField).x, y: F (unwrap dummyStepSgInWrapField).y }
      , dummyPrevEvals: dummyPrevEvalsMax
      -- A padded slot's wrap-domain index is `one`, not zero: the
      -- wrap circuit expects index 1 of `[13, 14, 15]` — its own
      -- domain — for a dummy slot.
      , dummyPrevWrapDomainIdx: F one
      , dummyKimchiPrevEntry:
          { sgX: (unwrap dummyWrapSgInStepField).x
          , sgY: (unwrap dummyWrapSgInStepField).y
          , challenges: dummyIpaChallenges.wrapExpanded
          }
      , dummySlotChal: map F dummyIpaChallenges.wrapExpanded
      }

    proveDataMax = padShapeProveData padDummies wrapResult.slotWidths proveData

  eStepResult <- r.stepProveFn handler shape.stepProveCtx stepCR stepAdvice
  case eStepResult of
    Left e -> pure (Left e)
    Right stepResult -> do

      let
        stepOraclesPrevChals = Vector.toUnfoldable $
          Vector.zipWith
            ( \(AffinePoint sg) chals ->
                { sgX: sg.x
                , sgY: sg.y
                , challenges: Vector.toUnfoldable chals
                }
            )
            proveData.prevSgs
            proveData.prevStepChallenges

        stepOracles = proofOraclesRec stepCR.verifierIndex
          { proof: stepResult.proof
          , publicInput: stepResult.publicInputs
          , prevChallenges: stepOraclesPrevChals
          }

        -- The step proof's evaluations, one `PointEval` per
        -- polynomial per chunk, which the wrap prover consumes as-is.
        stepProofData = pallasProofData @StepIPARounds stepResult.proof
        chunkedEvals =
          { ftEval1: stepOracles.ftEval1
          -- The public evaluation comes from the proof, which carries
          -- all `nc` chunks, and not from `stepOracles.publicEvals`,
          -- which the oracle binding has already collapsed to chunk
          -- zero: the chunked fold below needs every chunk.
          , publicEvals: stepProofData.evals.public
          , zEvals: stepProofData.evals.z
          , witnessEvals: stepProofData.evals.w
          , coeffEvals: stepProofData.evals.coefficients
          , sigmaEvals: stepProofData.evals.s
          , indexEvals: stepProofData.evals.indexEvals
          }

        -- The Horner-combined view of `chunkedEvals`, carried on the
        -- `CompiledProof` for the recursive-step consumers that take
        -- a single-eval `AllEvals`: `Pickles.Prove.Step`'s
        -- `wrapPrevEvals` and `stepAdvicePrevEvals`.
        stepGenSelf = domainGenerator selfStepDomainLog2
        allEvals = collapseChunkedEvals
          { rounds: reflectType (Proxy :: Proxy StepIPARounds)
          , zeta: stepOracles.zeta
          , zetaOmega: stepOracles.zeta * stepGenSelf
          }
          chunkedEvals

        outerMpv = reflectType (Proxy @mpv)

        proofsVerifiedMask = (outerMpv >= 2) :< (outerMpv >= 1) :< Vector.nil

        selfZkRows = zkRowsForNumChunks (reflectType (Proxy :: Proxy stepChunks))

        wrapDvInput =
          { proof: stepResult.proof
          , verifierIndex: stepCR.verifierIndex
          , publicInput: stepResult.publicInputs
          , chunkedEvals
          , pEval0Chunks: map _.zeta (NonEmptyArray.toArray stepProofData.evals.public)
          , domainLog2: selfStepDomainLog2
          , zkRows: selfZkRows
          , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
          , generator: (domainGenerator selfStepDomainLog2)
          , shifts: (domainShifts selfStepDomainLog2)
          , vanishesOnZk: permutationVanishingPolynomial
              { domainLog2: selfStepDomainLog2
              , zkRows: selfZkRows
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

        -- The step public input is `mpvMax`-shaped, its unfinalized
        -- proofs front-padded up from the rule's own `mpv`, so the
        -- outer-hash digest sits at `mpvMax * 32` rather than at
        -- `mpv * 32`. The constraint chain in scope bounds that index
        -- by `outputSize`.
        msgStep =
          let
            F f = Vector.index stepResult.publicOutputs
              (unsafeFinite @outputSize (outerMpvMax * 32))
          in
            f

        stepProofSg = (pallasProofData @StepIPARounds stepResult.proof).opening.sg

        dummyWrapExpanded = dummyIpaChallenges.wrapExpanded

        -- Built from the same dummies as `padDummies` above, so both
        -- front-paddings come off one random-oracle stream. When
        -- `mpv < mpvMax`, two streams leave the wrap circuit's
        -- permutation argument unclosed.
        dummyKimchiEntry
          :: { sgX :: StepField
             , sgY :: StepField
             , challenges :: Vector WrapIPARounds WrapField
             }
        dummyKimchiEntry =
          { sgX: (unwrap dummyWrapSgInStepField).x
          , sgY: (unwrap dummyWrapSgInStepField).y
          , challenges: dummyIpaChallenges.wrapExpanded
          }

        msgWrapPadded =
          Vector.append (Vector.replicate @padMax dummyWrapExpanded)
            proveDataMax.msgWrapChallenges

        kimchiPrevPadded
          :: Vector PaddedLength
               { sgX :: StepField
               , sgY :: StepField
               , challenges :: Vector WrapIPARounds WrapField
               }
        kimchiPrevPadded =
          Vector.append (Vector.replicate @padMax dummyKimchiEntry)
            proveDataMax.kimchiPrevEntries

        msgWrap = hashMessagesForNextWrapProofPureGeneral
          { sg: stepProofSg
          , paddedChallenges: msgWrapPadded
          }

        wrapDv = wrapComputeDeferredValues wrapDvInput

        -- The wrap solver's context: statement, advice, and this
        -- branch's index as `whichBranch`.
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
          , advice: buildWrapAdvice @stepChunks
              { stepProof: stepResult.proof
              , whichBranch: F (fromBigInt (BigInt.fromInt branchIdx) :: WrapField)
              , prevUnfinalizedProofs: proveDataMax.prevUnfinalizedProofs
              , prevMessagesForNextStepProofHash:
                  F (fromBigInt (toBigInt msgStep) :: WrapField)
              , prevStepAccs: proveDataMax.prevStepAccs
              , prevOldBpChals: proveDataMax.slotsValue
              , prevEvals: proveDataMax.prevEvals
              , prevWrapDomainIndices: proveDataMax.prevWrapDomainIndices
              }
          , debug: cfg.debug
          , proofCache: cfg.proofCache
          , kimchiPrevChallenges: kimchiPrevPadded
          }

      eWrapProveResult <- wrapSolveAndProve @branches @mpvMax @stepChunks wrapCtx wrapResult
      case eWrapProveResult of
        Left e -> pure (Left e)
        Right wrapProveResult -> do

          let
            -- The rule's own public output, which is
            -- `userPublicOutputFields` — not `publicOutputs`, the
            -- kimchi public-output vector of digest, unfinalized
            -- proofs and wrap messages.
            publicOutput =
              fieldsToValue @StepField stepResult.userPublicOutputFields

          let
            widthData = mkSomeCompiledProofWidthData @mpv @pad
              { oldBulletproofChallenges: proveData.prevStepChallenges
              , msgWrapChallenges: proveData.msgWrapChallenges
              , outerStepChalPolyComms:
                  map (\e -> AffinePoint { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
              -- The padded views `mkSomeCompiledProofWidthData`
              -- precomputes must agree with what `mkStepAdvice` and
              -- `shapeProveData` put in the pad slots, so the same
              -- three dummies are handed over here.
              , dummyOldBp: dummyIpaChallenges.stepExpanded
              , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
              , dummyChalPolyComm: dummyWrapSgInStepField
              }

          let
            statement = StatementIO { input: appInput, output: publicOutput }

          pure $ Right $ CompiledProof
            { statement
            , wrapProof: wrapProveResult.proof
            , rawPlonk: toPlonkMinimal wrapDv.plonk
            , rawBulletproofChallenges: wrapDv.bulletproofPrechallenges
            , branchData: wrapDv.branchData
            , spongeDigestBeforeEvaluations: wrapDv.spongeDigestBeforeEvaluations
            , prevEvals: allEvals
            , prevEvalsChunked: chunkedEvals
            -- All `nc` chunks, as in `chunkedEvals` above; a
            -- recursive consumer reads them back here.
            , pEval0Chunks: map _.zeta (NonEmptyArray.toArray stepProofData.evals.public)
            , challengePolynomialCommitment: stepProofSg
            -- The statement's fields, input then output: what the
            -- step circuit hashed into the step message digest.
            , appState: valueToFields @StepField statement
            , widthData
            , stepDomainLog2: selfStepDomainLog2
            }

compileMulti
  :: forall @rs @outputVal @prevInputVal @stepChunks numChunksPred
       r
       inputVal mpvMax
       branches
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
       branchesPred totalBases totalBasesPred
       tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal
       branches
       branches
       mpvMax
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
       r
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpvMax Int
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
  => Compare 0 branches LT
  => Compare mpvMax 3 LT
  => Add mpvMax nonSgBases totalBases
  => Add 1 totalBasesPred totalBases
  => MaxOfRulesMpvs rs mpvMax
  => AdviceHandler r
  -> CompileMultiConfig
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
compileMulti handler cfg rules = do
  let
    slotWidths = deriveWrapSlotWidths (reflectType (Proxy :: Proxy mpvMax))
      ( ruleSlotWidths
          @rs
          @inputVal
          @outputVal
          @prevInputVal
          @branches
          @branches
          @mpvMax
          @rulesCarrier
          @stepCompileFnsCarrier
          @perBranchCtxsCarrier
          @perBranchStepCompileResults
          @stepProveFnsCarrier
          @r
          (Proxy :: Proxy rs)
      )
  -- Step 1: the per-rule pre-pass, then the per-rule step compiles
  -- against the domains it found.
  { stepResults, log2s } <- runMultiCompileFull
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @branches
    @mpvMax
    @r
    handler
    cfg
    (reflectType (Proxy :: Proxy stepChunks))
    rules

  -- The declared `@stepChunks` has to match what each branch's step
  -- domain actually needs: one chunk while the domain fits the
  -- maximum polynomial size, and `2^(log2 - StepIPARounds)` beyond
  -- it, which is kimchi's `domain_size / max_poly_size`.
  let
    declaredNumChunks = reflectType (Proxy :: Proxy stepChunks)
    stepMaxPolyLog2 = reflectType (Proxy :: Proxy StepIPARounds)
    branchNumChunks log2 =
      if log2 <= stepMaxPolyLog2 then 1
      else 1 `Int.Bits.shl` (log2 - stepMaxPolyLog2)
    perBranchActualVec = map branchNumChunks log2s
    perBranchActual = Vector.toUnfoldable perBranchActualVec :: Array Int
  case Array.find (_ /= declaredNumChunks) perBranchActual of
    Just bad ->
      Exc.throw $ "compileMulti: declared stepChunks=" <> show declaredNumChunks
        <> " but branch step circuit computes num_chunks="
        <> show bad
        <> " (per-branch step domain log2s: "
        <> show (Vector.toUnfoldable log2s :: Array Int)
        <> ", StepIPARounds (max_poly_log2)="
        <> show stepMaxPolyLog2
        <> ")"
    Nothing -> pure unit

  let
    perBranchVec = buildWrapPerBranchVec
      @rs
      @inputVal
      @outputVal
      @prevInputVal
      @branches
      @branches
      @mpvMax
      @rulesCarrier
      @stepCompileFnsCarrier
      @perBranchCtxsCarrier
      @perBranchStepCompileResults
      @stepProveFnsCarrier
      @r
      stepResults

  -- Step 2: shared wrap compile across all branches.
  wrapResult <- wrapCompile @branches @mpvMax @stepChunks
    { wrapMainConfig:
        buildWrapMainConfigMulti @branches cfg.srs.vestaSrs
          { perBranch: perBranchVec }
    , crs: cfg.srs.pallasSrs
    , slotWidths:
        case Vector.toVector slotWidths of
          Just ws -> ws
          Nothing -> unsafeThrow
            $ "compileMulti: expected "
                <> show (reflectType (Proxy :: Proxy mpvMax))
                <> " slot widths, got "
                <> show (Array.length slotWidths)
    }

  -- The wrap domain the step circuits were built against is an
  -- assumption. Every step circuit bakes it in before the wrap circuit
  -- exists, so a wrong assumption is not detected here; it surfaces much
  -- later as a failure inside the kimchi prover, on the first proof that
  -- verifies a real previous proof. Compare the assumption against the
  -- circuit that was actually built, and say which is which.
  let
    actualWrapDomainLog2 = ProofFFI.proverIndexDomainLog2 wrapResult.proverIndex
    assumedWrapDomainLog2 = case cfg.wrapDomainOverride of
      Just o -> o
      Nothing -> wrapDomainLog2ForProofsVerified (reflectType (Proxy :: Proxy mpvMax))
  -- `Exc.throw`, not `unsafeThrow`: the latter throws as soon as it is
  -- evaluated, which in a strict language is before `when` inspects the
  -- condition.
  when (actualWrapDomainLog2 /= assumedWrapDomainLog2)
    $ Exc.throw
    $ "compileMulti: this circuit was compiled for proofs using the wrap "
        <> "domain of size "
        <> show assumedWrapDomainLog2
        <> ", but the actual wrap domain size for the circuit has size "
        <> show actualWrapDomainLog2
        <> ". Set wrapDomainOverride to the correct domain size."

  -- Step 3: one prover closure per branch, each capturing its own
  -- index and sharing the step-domain vector.
  provers <- buildBranchProvers
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @branches
    @branches
    @mpvMax
    @rulesCarrier
    @stepCompileFnsCarrier
    @perBranchCtxsCarrier
    @perBranchStepCompileResults
    @stepProveFnsCarrier
    @proversCarrier
    @r
    (Proxy :: Proxy stepChunks)
    0
    cfg
    wrapResult
    perBranchVec
    log2s
    stepResults
    rules

  -- Step 4: shared verifier + tag.
  unique <- newUnique
  let
    -- The wrap circuit's own domain log2, which the verifier needs;
    -- the wrap circuit body itself picks per-branch lagrange bases
    -- through `perBranchLagrangeAt` instead.
    wrapDomainLog2 =
      wrapDomainLog2ForProofsVerified (reflectType (Proxy :: Proxy mpvMax))

    verifier = mkVerifier
      { wrapVK: wrapResult.verifierIndex
      , pallasSrs: cfg.srs.pallasSrs
      , vestaSrs: cfg.srs.vestaSrs
      , stepNumChunks: reflectType (Proxy :: Proxy stepChunks)
      }

  pure
    { provers
    , tag: wrap { unique, verifier }
    , verifier
    , vks:
        { wrap: wrapResult
        , perBranchStep: stepResults
        , wrapDomainLog2
        , stepChunks: reflectType (Proxy :: Proxy stepChunks)
        }
    , perBranchVKs: unit
    }
