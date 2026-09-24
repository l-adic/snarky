-- | The multi-branch pickles compile: `compileMulti`, and the
-- | machinery it dispatches through.
-- |
-- | Two levels of type-level list are at work. `SplitPrevs` is indexed
-- | by one rule's prev-slot spec and splits that rule's typed prevs
-- | into the statements the rule reads and one `SomePrevSlot` per
-- | slot, which the prover walks as a `Vector`;
-- | `CompilableRulesSpec` and `CompilableRulesSpecShape` are indexed
-- | by the list of rules and walk the branches. `RuleEntry` is one
-- | branch; `runMultiProverBody` is one branch's prover.
module Pickles.Prove.Compile
  ( PrevSlot(..)
  , SideLoadedPrev(..)
  , class SplitPrevs
  , splitPrevs
  , SomePrevSlot
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
  , padShapeProveData
  , class SlotKinds
  , slotKeysOf
  , class CompilableRulesSpec
  , ruleCompileFns
  , RuleCompileFns
  , CompileMultiConfig
  , class CompilableRulesSpecShape
  , class MaxOfRulesMpvs
  , class IntMax
  , class IntMaxOrd
  , buildBranchProvers
  , module Pickles.Verify
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either, note)
import Data.Enum (fromEnum)
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int.Bits as Int.Bits
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, over, unwrap, wrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence, traverse)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector, (!!), (:<))
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
import Pickles.PlonkChecks (collapseChunkedEvals, collapsePointEval, padChunkedEvals, singleChunkEvals)
import Pickles.ProofsVerified (ProofsVerified(..), allPossibleDomainLog2s, boolVecToProofsVerified)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Slot (CompiledTagData, SlotWrapKey(..), slotNumChunks, slotSourceDomainLog2s, slotWrapDomainLog2)
import Pickles.Prove.Slot as RuntimeSlot
import Pickles.Prove.Step
  ( SlotAdviceContrib
  , StepAdvice(..)
  , StepCompileResult
  , StepProveContext
  , buildSlotAdvice
  , dummyWrapTockPublicInput
  , extractWrapVKCommsAdvice
  , mkDummyMsgWrapHash
  )
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
import Pickles.Prove.Wrap
  ( WrapBranchData
  , WrapCompileResult
  , buildWrapAdvice
  , buildWrapMainConfigMulti
  , wrapCompile
  , wrapSolveAndProve
  )
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Sideload.Bundle (Bundle, projectVk, verifierIndex) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey(..)) as SLVK
import Pickles.Slots (Compiled, SideLoaded, SlotOf)
import Pickles.Step.Dummy
  ( baseCaseDummies
  , computeDummySgValues
  , dummyWrapProof
  , proofsVerifiedForWrapDomainLog2
  , wrapDomainLog2ForProofsVerified
  , wrapDummyUnfinalizedProof
  )
import Pickles.Step.Dummy as Dummy
import Pickles.Step.Slots (class SlotStatementsCarrier, class SlotWidths, SideLoadedPrevValue, SlotWidth, slotWidthInt, slotWidthsOf, withSlotWidth)
import Pickles.Step.Types as Step
import Pickles.Step.VkSource (SlotVkBlueprint(..))
import Pickles.Types (AllocEvals(..), PaddedLength, PerProofUnfinalized(..), StatementIO(..), StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (VerificationKey(..), verifierIndexDigest, vestaVerifierIndexCommitments)
import Pickles.Verify
  ( CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , Verifier
  , mkSomeCompiledProofWidthData
  , mkVerifier
  , prevProofDataOf
  , verify
  , wrapPublicInputVP
  )
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (EQ, GT, LT)
import Prim.Ordering as PrimOrdering
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (AdviceHandler, badAdvice)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..))
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
import Snarky.Backend.Kimchi.ProofCache (ProofCache, ProofRef, piKey)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL (F(..), UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF (unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (fromShifted, toShifted) as Kimchi
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue)
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
  { fopDomainLog2s :: NonEmptyArray Int
  , numChunks :: Int
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
  -> NonEmptyArray Int
  -> RuntimeSlot.Slot
  -> SlotCompileEntry slotNc
slotCompileEntry cfg selfStepDomainLog2s slot =
  { fopDomainLog2s: slotSourceDomainLog2s selfStepDomainLog2s slot
  , numChunks: slotNumChunks cfg.stepNumChunks slot
  , vkBlueprint: blueprint
  }
  where
  outer = cfg.outerWrapDomainLog2

  lagrangeAt :: Int -> Int -> Vector slotNc (AffinePoint (F StepField))
  lagrangeAt = lagrangeAtDomain cfg.pallasSrs

  slotLagrange = mkConstLagrangeBaseLookup (lagrangeAt (slotWrapDomainLog2 outer slot))

  blueprint = case slot.source of
    Just Self -> BlueprintSelf slotLagrange
    Just (External d) ->
      BlueprintExternal slotLagrange (externalWrapVk @slotNc d.wrapVerifierIndex)
    -- A side-loaded slot's wrap domain is not known until prove time,
    -- so it carries all three bases and muxes in-circuit instead.
    Nothing ->
      BlueprintSideLoaded (map (lagrangeAt <<< getFinite) allPossibleDomainLog2s)

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

type StepInputs :: Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier =
  { appInput :: inputVal
  -- | One entry per slot, in slot order: a `PrevSlot` for a compiled
  -- | slot, a `SideLoadedPrev` for a side-loaded one.
  , prevs :: prevsCarrier
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

-- | What the caller supplies for a side-loaded prev slot: the
-- | verification key the slot verifies against, with the slot's prev.
-- | Only a side-loaded slot takes one, so the type of `prevs` rules out
-- | both a missing key and a stray one.
data SideLoadedPrev :: Type -> Int -> Type -> Type
data SideLoadedPrev inputVal n stmt =
  SideLoadedPrev (SideloadBundle.Bundle WrapVkChunks) (PrevSlot inputVal n stmt)

-- | One `PrevSlot` with its type parameters hidden and its statement's
-- | `CircuitType` kept, so that the slots of a rule share one `Vector`
-- | whatever their statement types.
newtype SomePrevSlot = SomePrevSlot
  ( forall r
     . ( forall inputVal n stmt stmtVar
          . CircuitType StepField stmt stmtVar
         => PrevSlot inputVal n stmt
         -> r
       )
    -> r
  )

-- | Run `k` on the slot, at its own types.
withPrevSlot
  :: forall r
   . SomePrevSlot
  -> ( forall inputVal n stmt stmtVar
        . CircuitType StepField stmt stmtVar
       => PrevSlot inputVal n stmt
       -> r
     )
  -> r
withPrevSlot (SomePrevSlot run) k = run k

-- | A rule's typed prevs, split once at the prove call into the
-- | previous statements the rule reads as advice, typed per slot, and
-- | per slot for the prover, its prev and the key a side-loaded slot
-- | was given.
class SplitPrevs :: Type -> Type -> Type -> Int -> Constraint
class SplitPrevs spec prevsCarrier valCarrier len | spec -> prevsCarrier valCarrier len where
  splitPrevs
    :: forall proxy
     . proxy spec
    -> prevsCarrier
    -> { values :: valCarrier
       , slots ::
           Vector len
             { prev :: SomePrevSlot
             , sideLoadedKey :: Maybe (SideloadBundle.Bundle WrapVkChunks)
             }
       }

instance SplitPrevs Unit Unit Unit 0 where
  splitPrevs _ _ = { values: unit, slots: Vector.nil }

instance
  ( SplitPrevs rest restPrevs restValues restLen
  , Add restLen 1 len
  , CircuitType StepField input inputVar
  , CircuitType StepField output outputVar
  ) =>
  SplitPrevs
    (SlotOf Compiled n (StatementIO input output) /\ rest)
    (PrevSlot input n (StatementIO input output) /\ restPrevs)
    (StatementIO input output /\ restValues)
    len
  where
  splitPrevs _ (prev /\ rest) =
    let
      r = splitPrevs (Proxy :: Proxy rest) rest
    in
      { values: statementOf prev /\ r.values
      , slots: Vector.cons
          { prev: SomePrevSlot \k -> k prev, sideLoadedKey: Nothing }
          r.slots
      }

instance
  ( SplitPrevs rest restPrevs restValues restLen
  , Add restLen 1 len
  , CircuitType StepField input inputVar
  , CircuitType StepField output outputVar
  ) =>
  SplitPrevs
    (SlotOf SideLoaded n (StatementIO input output) /\ rest)
    (SideLoadedPrev input n (StatementIO input output) /\ restPrevs)
    (SideLoadedPrevValue (StatementIO input output) /\ restValues)
    len
  where
  splitPrevs _ (SideLoadedPrev key prev /\ rest) =
    let
      r = splitPrevs (Proxy :: Proxy rest) rest
    in
      { values:
          { statement: statementOf prev
          , verificationKey: SideloadBundle.projectVk key
          } /\ r.values
      , slots: Vector.cons
          { prev: SomePrevSlot \k -> k prev, sideLoadedKey: Just key }
          r.slots
      }

-- | The prev's statement, whichever way its slot is filled.
statementOf :: forall inputVal n stmt. PrevSlot inputVal n stmt -> stmt
statementOf = case _ of
  BasePrev { dummyStatement } -> dummyStatement
  InductivePrev (CompiledProof p) _ -> p.statement

type CompileConfig :: Int -> Type
type CompileConfig mpv =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -- | Where each slot's wrap VK comes from, in slot order: a compiled
  -- | slot's key, or `Nothing` for a side-loaded slot.
  , perSlotImportedVKs :: Vector mpv (Maybe SlotWrapKey)
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

-- | A side-loaded slot's wrap domain log2, decoded from its runtime
-- | VK descriptor's length-3 one-hot `actualWrapDomainSize` vector.
bundleWrapDomainLog2 :: forall nc. SideloadBundle.Bundle nc -> Int
bundleWrapDomainLog2 =
  Dummy.wrapDomainLog2ForProofsVerified <<< fromEnum <<< bundleWrapDomain

-- | A side-loaded key's wrap domain, as the `proofs_verified` that
-- | indexes it.
bundleWrapDomain :: forall nc. SideloadBundle.Bundle nc -> ProofsVerified
bundleWrapDomain bundle =
  boolVecToProofsVerified
    ( case SideloadBundle.projectVk bundle of
        SLVK.VerificationKey vkRec -> vkRec.actualWrapDomainSize
    )

-- | The wrap domain the wrap circuit pins a slot's finalize check to:
-- | the compile's own for `Self`, the imported tag's for `External`;
-- | `Nothing` for a side-loaded slot, whose domain arrives with its
-- | runtime key. A wrap domain outside the table fails the compile, as
-- | OCaml's `domain_index` does.
slotWrapDomainPin :: Int -> Maybe SlotWrapKey -> Either String (Maybe ProofsVerified)
slotWrapDomainPin selfWrapDomainLog2 = case _ of
  Just Self -> Just <$> known selfWrapDomainLog2
  Just (External d) -> Just <$> known d.wrapDomainLog2
  Nothing -> Right Nothing
  where
  known log2 = note
    ("compileMulti: a prev slot's wrap domain log2 " <> show log2 <> " is not a wrap domain")
    (proofsVerifiedForWrapDomainLog2 log2)

-- | The wrap domain a padding slot is pinned to and the prover supplies
-- | for it: OCaml's `Tock.Field.one` in `Wrap_domain_indices`.
paddingWrapDomain :: ProofsVerified
paddingWrapDomain = N1

-- | One rule's `StepProveContext`: the shared SRS data, then one entry
-- | per slot, from that slot's width and `SlotWrapKey`.
-- |
-- | `selfStepDomainLog2s` holds every branch's own step domain log2,
-- | which is what a `Self` slot's source domains are; an `External`
-- | slot ignores it and reads the imported rule's step domain off its
-- | prover index. During the pre-pass, which only counts gates,
-- | callers pass `roughDomainsLog2` in every position.
stepProveContextOf
  :: forall mpv
   . Reflectable mpv Int
  => CompileConfig mpv
  -> Vector mpv Int
  -> NonEmptyArray Int
  -> StepProveContext mpv
stepProveContextOf cfg slotWidths selfStepDomainLog2s =
  { srsData:
      { blindingH:
          coerce (ProofFFI.srsBlindingGenerator cfg.srs.pallasSrs :: AffinePoint StepField)
      , perSlotFopDomainLog2s: map _.fopDomainLog2s entries
      , perSlotNumChunks: map _.numChunks entries
      , perSlotVkBlueprints: map _.vkBlueprint entries
      }
  , dummySg: outerDummySgs.ipa.wrap.sg
  , crs: cfg.srs.vestaSrs
  , debug: cfg.debug
  , proofCache: cfg.proofCache
  }
  where
  entries = Vector.zipWith
    ( \width key -> slotCompileEntry @WrapVkChunks
        { pallasSrs: cfg.srs.pallasSrs
        , stepNumChunks: cfg.stepNumChunks
        , outerWrapDomainLog2: cfg.selfWrapDomainLog2
        }
        selfStepDomainLog2s
        { localMpv: width, source: key }
    )
    slotWidths
    cfg.perSlotImportedVKs

  outerBcd = Dummy.baseCaseDummies
    { maxProofsVerified: reflectType (Proxy :: Proxy mpv) }
  outerDummySgs =
    Dummy.computeDummySgValues outerBcd cfg.srs.pallasSrs cfg.srs.vestaSrs

-- | What one slot contributes to the step prover's advice: its
-- | oracle-enriched witness, its wrap public input, and the cache key
-- | of the wrap proof it verifies, if it verifies one.
slotStepAdvice
  :: forall w wPad inputVal input prevHeadInput n prevHeadStmt prevHeadStmtVar
   . Reflectable w Int
  => Compare w 3 LT
  => Reflectable wPad Int
  => Add wPad w PaddedLength
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => Proxy w
  -> { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -> inputVal
  -> { slotWrapVK :: VerifierIndex PallasG WrapField
     , slotWrapDomainLog2 :: Int
     , slotStepDomainLog2 :: Int
     , slotStepZkRows :: Int
     , slotWrapZkRows :: Int
     , slotStepNumChunks :: Int
     }
  -> PrevSlot prevHeadInput n prevHeadStmt
  -> Effect
       { contrib :: SlotAdviceContrib
       , wrapPublicInput :: Array WrapField
       , proofRef :: Maybe ProofRef
       }
slotStepAdvice _ srs appInput slotParams headSlot = do
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
    , wrapPrevEvalsChunked: slotData.wrapPrevEvalsChunked
    , wrapBranchData: slotData.wrapBranchData
    , wrapSpongeDigest: slotData.wrapSpongeDigest
    , mustVerify: slotData.mustVerify
    , wrapOwnPaddedBpChals: slotData.wrapOwnPaddedBpChals
    , fopState: slotData.fopState
    , stepAdvicePrevEvals: slotData.stepAdvicePrevEvals
    , kimchiPrevChallengesExpanded: slotData.kimchiPrevChallengesExpanded
    , prevChallengesForStepHash: slotData.prevChallengesForStepHash
    }
  pure
    { contrib
    , wrapPublicInput: slotData.wrapPublicInputArr
    -- A base-case slot's dummy proof is not cached.
    , proofRef:
        if slotData.mustVerify then
          Just
            { vkDigest: BigInt.toString (toBigInt (verifierIndexDigest slotParams.slotWrapVK))
            , publicInput: piKey slotData.wrapPublicInputArr
            }
        else Nothing
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
          { domainLog2: slotParams.slotStepDomainLog2
          , zkRows: slotParams.slotStepZkRows
          , numChunks: slotParams.slotStepNumChunks
          }
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
        , wrapPrevEvalsChunked: padChunkedEvals slotParams.slotStepNumChunks (singleChunkEvals bcd.proofDummy.prevEvals)
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
        , stepAdvicePrevEvals: padChunkedEvals slotParams.slotStepNumChunks (singleChunkEvals bcd.proofDummy.prevEvals)
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
        , wrapPrevEvalsChunked: prevData.proof.prevEvalsChunked
        , wrapBranchData: prevData.proof.branchData
        , wrapSpongeDigest: prevData.proof.spongeDigestBeforeEvaluations
        , mustVerify: true
        , wrapOwnPaddedBpChals: prevData.padded.msgWrapChallengesPadded
        , fopState
        , stepAdvicePrevEvals: prevData.proof.prevEvalsChunked
        , kimchiPrevChallengesExpanded: prevStepBpChalsExpanded
        , prevChallengesForStepHash: prevData.padded.oldBulletproofChallengesPadded
        }

-- | What one slot contributes to the wrap prover's inputs.
-- |
-- | `slotParams` is everything that varies by slot source: the wrap
-- | verifier index, the wrap domain, the slot's width and the padding
-- | that width implies. A compiled slot resolves them from the
-- | enclosing or the imported compile, a side-loaded slot off its
-- | runtime key. `stepSide` is this slot's entry of what
-- | `mkStepAdvice` returned.
slotProveData
  :: forall prevHeadInput n stmt stmtVar
   . CircuitType StepField stmt stmtVar
  => { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -> { slotWrapVK :: VerifierIndex PallasG WrapField
     , slotWrapDomain :: ProofsVerified
     , slotWidth :: Int
     , slotPad :: Int
     }
  -> { challengePolynomialCommitment :: AffinePoint StepField
     , unfinalized ::
         PerProofUnfinalized WrapIPARounds
           (Type2 (SplitField (F StepField) Boolean))
           (F StepField)
           Boolean
     , baseCaseWrapPublicInput :: Array WrapField
     }
  -> PrevSlot prevHeadInput n stmt
  -> SlotProveData
slotProveData srs slotParams stepSide headSlot =
  { prevSg: slotData.prevSg
  , prevStepChallenges: slotData.prevStepChals
  , msgWrapChallenges: msgForNextWrapRealChals
  , prevUnfinalizedProof: headUnfinalizedWrap
  , prevStepAcc: slotData.prevStepAcc
  , prevEvals: slotData.headPrevEvals
  , prevWrapDomainIndex: slotParams.slotWrapDomain
  , kimchiPrevEntry:
      { sgX: (unwrap headChalPolyComm).x
      , sgY: (unwrap headChalPolyComm).y
      , challenges: msgForNextWrapRealChals
      }
  , prevWrapBpChals: slotData.headSlotPrevWrapBpChals
  }
  where
  -- Dummies sized by the slot's own width, not the enclosing rule's:
  -- a rule's slots can have different widths, and each slot's dummies
  -- have to match its own.
  bcd = Dummy.baseCaseDummies { maxProofsVerified: slotParams.slotWidth }
  dummySgs = Dummy.computeDummySgValues bcd srs.pallasSrs srs.vestaSrs
  stepSgD = dummySgs.ipa.step.sg -- AffinePoint WrapField

  PerProofUnfinalized headUnfRaw = stepSide.unfinalized
  headChalPolyComm = stepSide.challengePolynomialCommitment
  headBaseCaseWrapPI = stepSide.baseCaseWrapPublicInput

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
              prevWrapOracles.zeta
                * domainGenerator
                    (wrapDomainLog2ForProofsVerified (fromEnum slotParams.slotWrapDomain))
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
  , prevWrapDomainIndices :: Vector mpv ProofsVerified
  , kimchiPrevEntries ::
      Vector mpv
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  -- | Each prev's wrap bulletproof challenge stacks, in slot order.
  , slotsValue :: Array (Array (Vector WrapIPARounds (F WrapField)))
  }

-- | One slot's entry of every `ShapeProveData` field.
type SlotProveData =
  { prevSg :: AffinePoint WrapField
  , prevStepChallenges :: Vector StepIPARounds StepField
  , msgWrapChallenges :: Vector WrapIPARounds WrapField
  , prevUnfinalizedProof ::
      PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean
  , prevStepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
  , prevEvals :: AllocEvals (F WrapField)
  , prevWrapDomainIndex :: ProofsVerified
  , kimchiPrevEntry ::
      { sgX :: StepField
      , sgY :: StepField
      , challenges :: Vector WrapIPARounds WrapField
      }
  , prevWrapBpChals :: Array (Vector WrapIPARounds (F WrapField))
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
      Vector.append (Vector.replicate @mpvPad paddingWrapDomain)
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
-- The prove call's per-slot data
--------------------------------------------------------------------------------

-- | The step solver's advice, plus what the wrap stage needs from it,
-- | built slot by slot in slot order: each slot's oracle work runs
-- | before the next slot's.
mkStepAdvice
  :: forall prevsSpec inputVal inputVar mpv valCarrier
   . CircuitType StepField inputVal inputVar
  => Reflectable mpv Int
  => CompileConfig mpv
  -> StepCompileResult
  -> WrapCompileResult
  -> inputVal
  -> Vector mpv SlotWidth
  -> valCarrier
  -> Vector mpv
       { prev :: SomePrevSlot
       , sideLoadedKey :: Maybe (SideloadBundle.Bundle WrapVkChunks)
       }
  -> Effect
       { stepAdvice ::
           StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal mpv
             valCarrier
       , challengePolynomialCommitments :: Vector mpv (AffinePoint StepField)
       , baseCaseWrapPublicInputs :: Vector mpv (Array WrapField)
       , prevProofRefs :: Array (Maybe ProofRef)
       }
mkStepAdvice cfg stepCR wrapCR appInput widths values slots = do
  perSlot <- forWithIndex slots \i slot ->
    withSlotWidth (widths !! i) \width ->
      withPrevSlot slot.prev \prev ->
        slotStepAdvice width cfg.srs appInput (slotParams i slot) prev
  pure
    { stepAdvice: StepAdvice
        { perProofSlotsCarrier: map _.contrib.slotSppw perSlot
        , publicInput: appInput
        , publicUnfinalizedProofs: map _.contrib.slotUnfinalized perSlot
        , messagesForNextWrapProof: map _.contrib.slotMsgWrapHashStep perSlot
        -- At `maxProofsVerified = 0` whatever the rule's width.
        , messagesForNextWrapProofDummyHash:
            mkDummyMsgWrapHash (Dummy.baseCaseDummies { maxProofsVerified: 0 })
              cfg.srs.pallasSrs
              cfg.srs.vestaSrs
        , wrapVerifierIndex: extractWrapVKCommsAdvice wrapCR.verifierIndex
        , kimchiPrevChallenges: map _.contrib.slotKimchiPrevEntry perSlot
        , prevAppStates: values
        }
    , challengePolynomialCommitments: map _.contrib.challengePolynomialCommitment perSlot
    , baseCaseWrapPublicInputs: map _.wrapPublicInput perSlot
    , prevProofRefs: Array.fromFoldable (map _.proofRef perSlot)
    }
  where
  -- A side-loaded slot's wrap VK is a runtime witness, so its domains
  -- come off the key rather than off anything this compile knows. The
  -- witness is still sized at the slot's compile-time bound; a smaller
  -- `actualWrapDomainSize` is masked in-circuit. A slot has a key
  -- exactly when the prevs spec makes it side-loaded, which is also
  -- when its entry of `perSlotImportedVKs` is `Nothing`.
  slotParams i slot = case slot.sideLoadedKey of
    Just bundle ->
      { slotWrapVK: SideloadBundle.verifierIndex bundle
      , slotWrapDomainLog2: bundleWrapDomainLog2 bundle
      , slotStepDomainLog2:
          -- A side-loaded VK does not carry the prev's step domain;
          -- the step circuit dispatches over `[0..16]` in
          -- `Pickles.Step.FinalizeOtherProof`'s `SideLoadedMode`.
          -- This stand-in reaches only the `BasePrev` site, where
          -- `proofMustVerify` is `false`; `InductivePrev` reads the
          -- prev's own `stepDomainLog2`.
          Dummy.wrapDomainLog2ForProofsVerified width
      -- A side-loaded proof is always single-chunk: the side-loaded
      -- domain dispatch varies the domain log2, not the chunk count.
      , slotStepZkRows: zkRowsForNumChunks 1
      , slotWrapZkRows: zkRowsForNumChunks 1
      , slotStepNumChunks: 1
      }
    Nothing ->
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
      , slotStepNumChunks: RuntimeSlot.slotNumChunks cfg.stepNumChunks runtimeSlot
      }
    where
    width = slotWidthInt (widths !! i)
    runtimeSlot = { localMpv: width, source: cfg.perSlotImportedVKs !! i }

-- | The rule's wrap-stage data, built slot by slot from the prevs, the
-- | step-advice side info and the slots' wrap-domain pins.
shapeProveData
  :: forall mpv
   . Reflectable mpv Int
  => CompileConfig mpv
  -> WrapCompileResult
  -> ShapeProveSideInfo mpv
  -> Vector mpv (Maybe ProofsVerified)
  -> Vector mpv SlotWidth
  -> Vector mpv
       { prev :: SomePrevSlot
       , sideLoadedKey :: Maybe (SideloadBundle.Bundle WrapVkChunks)
       }
  -> ShapeProveData mpv
shapeProveData cfg wrapCR sideInfo pins widths slots =
  { prevSgs: map _.prevSg perSlot
  , prevStepChallenges: map _.prevStepChallenges perSlot
  , msgWrapChallenges: map _.msgWrapChallenges perSlot
  , prevUnfinalizedProofs: map _.prevUnfinalizedProof perSlot
  , prevStepAccs: map _.prevStepAcc perSlot
  , prevEvals: map _.prevEvals perSlot
  , prevWrapDomainIndices: map _.prevWrapDomainIndex perSlot
  , kimchiPrevEntries: map _.kimchiPrevEntry perSlot
  , slotsValue: Array.fromFoldable (map _.prevWrapBpChals perSlot)
  }
  where
  perSlot = mapWithIndex
    ( \i slot -> withPrevSlot slot.prev \prev ->
        slotProveData cfg.srs (slotParams i slot)
          { challengePolynomialCommitment: sideInfo.challengePolynomialCommitments !! i
          , unfinalized: sideInfo.unfinalizedSlots !! i
          , baseCaseWrapPublicInput: sideInfo.baseCaseWrapPublicInputs !! i
          }
          prev
    )
    slots

  -- A `Self` slot verifies a proof of this same system, so it reads
  -- this compile's own wrap VK; an `External` slot reads the imported
  -- compile's, which that compile stored; a side-loaded slot reads it
  -- off its key. The wrap domain is the one the wrap circuit pins,
  -- which it does for every slot but a side-loaded one, whose domain
  -- comes with its key.
  slotParams i slot =
    { slotWrapVK: case slot.sideLoadedKey, cfg.perSlotImportedVKs !! i of
        Just bundle, _ -> SideloadBundle.verifierIndex bundle
        Nothing, Just (External d) -> d.wrapVerifierIndex
        Nothing, _ -> wrapCR.verifierIndex
    , slotWrapDomain: case slot.sideLoadedKey of
        Just bundle -> bundleWrapDomain bundle
        Nothing -> fromMaybe paddingWrapDomain (pins !! i)
    , slotWidth: width
    , slotPad: reflectType (Proxy :: Proxy PaddedLength) - width
    }
    where
    width = slotWidthInt (widths !! i)

--------------------------------------------------------------------------------
-- Type-level rules spec
--
-- The same idea as `Pickles.Step.Slots.PrevsSpec` one level up: a list
-- over the branches rather than over one branch's prev slots. Each
-- `RulesCons` carries the two facts that vary per branch — that
-- branch's `mpv` and its prevs spec, which fixes each slot's statement
-- type.
--
-- `inputVal` and `outputVal` are not among them: they parameterize the
-- shared wrap VK's public-input layout, so they live at the
-- multi-branch level.
--------------------------------------------------------------------------------

-- | Kind: a type-level list of rule specs.
data RulesSpec

-- | The empty rules list, which terminates the instance recursion.
-- | `compileMulti` itself rejects it, through `Compare 0 branches LT`.
foreign import data RulesNil :: RulesSpec

-- | One branch's contribution to the rules list: its `mpv`, its prevs
-- | spec, and the rest of the list.
foreign import data RulesCons :: Int -> Type -> RulesSpec -> RulesSpec

-- | `spec` → the number of its compiled slots, and each slot's key:
-- | a compiled slot takes the caller's next key, a side-loaded slot
-- | `Nothing`. The caller supplies keys for the compiled slots only, so
-- | a key's slot kind cannot disagree with the spec.
class SlotKinds :: Type -> Int -> Int -> Constraint
class SlotKinds spec compiled len | spec -> compiled len where
  slotKeysOf
    :: forall proxy
     . proxy spec
    -> Vector compiled SlotWrapKey
    -> Vector len (Maybe SlotWrapKey)

instance SlotKinds Unit 0 0 where
  slotKeysOf _ _ = Vector.nil

instance
  ( SlotKinds rest restCompiled restLen
  , Add restCompiled 1 compiled
  , Add 1 restCompiled compiled
  , Add restLen 1 len
  ) =>
  SlotKinds (SlotOf Compiled n stmt /\ rest) compiled len where
  slotKeysOf _ keys =
    let
      { head, tail } = Vector.uncons keys
    in
      Vector.cons (Just head) (slotKeysOf (Proxy :: Proxy rest) tail)

instance
  ( SlotKinds rest compiled restLen
  , Add restLen 1 len
  ) =>
  SlotKinds (SlotOf SideLoaded n stmt /\ rest) compiled len where
  slotKeysOf _ keys = Vector.cons Nothing (slotKeysOf (Proxy :: Proxy rest) keys)

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
  MaxOfRulesMpvs (RulesCons ruleMpv prevsSpec rest) mpvMax

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
  :: Type -> Int -> Type -> Type -> Type -> Row (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier inputVal outputVal r =
  BranchProver
    ( AdviceHandler r
      -> StepInputs prevsSpec inputVal prevsCarrier
      -> Effect (Either ProveError (CompiledProof mpv (StatementIO inputVal outputVal)))
    )

-- | A multi-branch compile's verification keys: one `wrap` VK, under
-- | which every branch's wrap proof verifies — the wrap statement's
-- | `whichBranch` says which step circuit was wrapped — and one
-- | `StepCompileResult` per branch, which are not shared.
type MultiVKs branches =
  { wrap :: WrapCompileResult
  , perBranchStep :: Vector branches PProveStep.StepCompileResult
  , wrapDomainLog2 :: Int
  -- | The compile's declared `@stepChunks`.
  , stepChunks :: Int
  }

-- | What `compileMulti` returns: one prover per branch, and one
-- | shared `tag`, `verifier` and set of VKs.
type MultiOutput
  :: Type
  -> Int
  -> Int
  -> Type
  -> Type
  -> Type
type MultiOutput proversCarrier branches mpvMax inputVal outputVal =
  { provers :: proversCarrier
  , tag :: Tag (StatementIO inputVal outputVal) mpvMax
  , verifier :: Verifier
  , vks :: MultiVKs branches
  -- | What an `External` slot of a later compile imports from this
  -- | one: pass it as `External tagData`.
  , tagData :: CompiledTagData
  }

--------------------------------------------------------------------------------
-- CompilableRulesSpec
--
-- The rules carrier is a tuple of `RuleEntry`s at different types;
-- one instance per rule collects each entry's `RuleCompileFns` into a
-- `Vector`, which the compile then walks as data.
--------------------------------------------------------------------------------

-- | One instance per rule, walking the rules spec.
-- |
-- | Two branch counts appear. `topBranches` is the whole compile's
-- | count and stays fixed through the recursion; `branches` is the
-- | count of the tail still to be walked. A `Self` slot's candidate
-- | step domains are all `topBranches` branches', not just the
-- | tail's.
class CompilableRulesSpec
  :: RulesSpec
  -> Type
  -> Type
  -> Int
  -> Int
  -> Int
  -> Type
  -> Row (Type -> Type)
  -> Constraint
class
  CompilableRulesSpec
    rs
    inputVal
    outputVal
    topBranches
    branches
    mpvMax
    rulesCarrier
    r
  | rs topBranches r ->
    branches mpvMax rulesCarrier
  where
  -- | Each rule's compile-time operations, in branch order.
  ruleCompileFns :: rulesCarrier -> Vector branches (RuleCompileFns mpvMax)

instance
  CompilableRulesSpec RulesNil
    inputVal
    outputVal
    topBranches
    0
    mpvMax
    Unit
    r
  where
  ruleCompileFns _ = Vector.nil

instance
  ( CompilableRulesSpec rest inputVal outputVal
      topBranches
      restBranches
      mpvMax
      restCarrier
      r
  , Add 1 restBranches branches
  , Add restBranches 1 branches
  -- The rule's slots front-padded to the wrap circuit's `mpvMax`.
  , Add mpvPad ruleMpv mpvMax
  , Reflectable mpvPad Int
  , SlotWidths prevsSpec ruleMpv
  -- `outputSize` derives from `mpvMax`, not from the rule's own
  -- `mpv`: the step public input is `mpvMax`-shaped.
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , Reflectable ruleMpv Int
  , SlotStatementsCarrier prevsSpec valCarrier
  ) =>
  CompilableRulesSpec
    (RulesCons ruleMpv prevsSpec rest)
    inputVal
    outputVal
    topBranches
    branches
    mpvMax
    ( RuleEntry prevsSpec ruleMpv mpvMax valCarrier inputVal outputSize r
        /\ restCarrier
    )
    r
  where
  ruleCompileFns (RuleEntry r /\ rest) =
    r.compileFns :< ruleCompileFns
      @rest
      @inputVal
      @outputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @r
      rest

--------------------------------------------------------------------------------
-- CompilableRulesSpecShape — shape-data methods.
--
-- Separate from `CompilableRulesSpec` because that class must not
-- carry a `SplitPrevs` super-constraint: PS cannot always
-- discharge one at a call site, and the failure cascades through the
-- funDep chain and leaves every class parameter unresolved. Split,
-- the structural methods stay light and only callers of the
-- shape-data methods take on the heavier discharge.
--------------------------------------------------------------------------------

class
  CompilableRulesSpec rs inputVal outputVal topBranches branches mpvMax
    rulesCarrier
    r <=
  CompilableRulesSpecShape
    rs
    inputVal
    outputVal
    topBranches
    branches
    mpvMax
    rulesCarrier
    proversCarrier
    r
  | rs topBranches r -> branches mpvMax rulesCarrier
    proversCarrier
  where
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
    -> Vector vecLen (WrapBranchData mpvMax)
    -- ^ every branch's wrap data
    -> Vector branches (Vector mpvMax (Maybe ProofsVerified))
    -- ^ the wrap-domain pins of this and the later branches
    -> Vector topBranches Int
    -> Vector branches PProveStep.StepCompileResult
    -> rulesCarrier
    -> Effect proversCarrier

-- | The per-branch step compiles, and the step domain log2s the
-- | pre-pass found for them. The pre-pass builds each rule's
-- | constraint system with `roughDomainsLog2` in every branch's
-- | position and counts its gates; the compiles then run against the
-- | domains it found.
runMultiCompileFull
  :: forall branches branchesPred mpvMax
   . Add 1 branchesPred branches
  => CompileMultiConfig
  -> Int
  -- ^ the declared `@stepChunks`
  -> Vector branches (RuleCompileFns mpvMax)
  -> Effect
       { stepResults :: Vector branches PProveStep.StepCompileResult
       , log2s :: Vector branches Int
       }
runMultiCompileFull cfg stepNumChunks rules = do
  let
    placeholder = NonEmptyArray.fromFoldable1 (map (const roughDomainsLog2) rules)
  log2s <- traverse (\rule -> rule.preComputeStepDomainLog2 cfg stepNumChunks placeholder) rules
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
  let
    selfStepDomainLog2s = NonEmptyArray.fromFoldable1 log2s
  stepResults <- traverse
    (\rule -> rule.stepCompile cfg stepNumChunks selfStepDomainLog2s)
    rules
  pure { stepResults, log2s }

instance
  CompilableRulesSpecShape RulesNil
    inputVal
    outputVal
    topBranches
    0
    mpvMax
    Unit
    Unit
    r
  where
  buildBranchProvers _ _ _ _ _ _ _ _ _ = pure unit

instance
  ( CompilableRulesSpecShape rest inputVal outputVal
      topBranches
      restBranches
      mpvMax
      restCarrier
      restProvers
      r
  , SplitPrevs prevsSpec prevsCarrier valCarrier ruleMpv
  , SlotWidths prevsSpec ruleMpv
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
  , CheckedType StepField (KimchiConstraint StepField) inputVar
  , CompilableRulesSpec
      (RulesCons ruleMpv prevsSpec rest)
      inputVal
      outputVal
      topBranches
      branches
      mpvMax
      ( RuleEntry prevsSpec ruleMpv mpvMax valCarrier inputVal outputSize r
          /\ restCarrier
      )
      r
  , Add 1 restBranches branches
  -- `(:<)` needs `Add restBranches 1 branches`; PS does not commute
  -- `Add`, so both orderings are stated.
  , Add restBranches 1 branches
  ) =>
  CompilableRulesSpecShape
    (RulesCons ruleMpv prevsSpec rest)
    inputVal
    outputVal
    topBranches
    branches
    mpvMax
    ( RuleEntry prevsSpec ruleMpv mpvMax valCarrier inputVal outputSize r
        /\ restCarrier
    )
    -- `BranchProver`'s `mpv` is `mpvMax`, not `ruleMpv`: every
    -- branch's `CompiledProof` presents the wrap-level width, with
    -- its own width hidden inside `widthData`. `BranchProver` is a
    -- newtype rather than an alias so that the instance head shows PS
    -- a saturated type constructor instead of a function type.
    ( BranchProver prevsSpec mpvMax prevsCarrier inputVal outputVal r
        /\ restProvers
    )
    r
  where
  buildBranchProvers
    ncProxy
    branchIdx
    cfg
    wrapResult
    perBranchVec
    pins
    allStepDomainLog2s
    stepResults
    (headEntry /\ restEntries) = do
    let
      { head: headPins, tail: restPins } = Vector.uncons pins
      { head: headStepCR, tail: restStepResults } = Vector.uncons stepResults
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
          @inputVal
          @inputVar
          @outputVal
          @outputVar
          @topBranches
          @mpvMax
          @mpvPad
          handler
          ncProxy
          thisBranch
          cfg
          wrapResult
          perBranchVec
          headPins
          allStepDomainLog2s
          headStepCR
          headLog2
          headEntry
          stepInputs
    restProvers <- buildBranchProvers
      @rest
      @inputVal
      @outputVal
      @topBranches
      @restBranches
      @mpvMax
      @restCarrier
      @restProvers
      @r
      ncProxy
      (branchIdx + 1)
      cfg
      wrapResult
      perBranchVec
      restPins
      allStepDomainLog2s
      restStepResults
      restEntries
    pure (headProver /\ restProvers)

--------------------------------------------------------------------------------
-- RuleEntry / mkRuleEntry — per-rule entry in the multi-branch carrier.
--------------------------------------------------------------------------------

-- | One rule's compile-time operations, with the rule's own types
-- | applied by `mkRuleEntry`, so that the compile walks the rules as a
-- | `Vector`. The `Int` arguments are the declared `@stepChunks` and,
-- | for `wrapBranchData`, the compile's own wrap domain log2; the
-- | `NonEmptyArray` is every branch's step domain log2, which a `Self`
-- | slot's finalize check selects among.
type RuleCompileFns mpvMax =
  { -- | The rule's slot widths, in slot order.
    slotWidths :: Array Int
  -- | The rule's step domain log2, counted from a constraint-system
  -- | build against placeholder domains.
  , preComputeStepDomainLog2 ::
      CompileMultiConfig -> Int -> NonEmptyArray Int -> Effect Int
  -- | The rule's step compile, after checking that each slot's
  -- | candidate domains share their shifts.
  , stepCompile ::
      CompileMultiConfig
      -> Int
      -> NonEmptyArray Int
      -> Effect PProveStep.StepCompileResult
  -- | The rule's entry in the wrap circuit's per-branch data: its
  -- | `mpv`, step domain, step VK, and each slot's wrap-domain pin,
  -- | padding slots first. `Left` names a slot whose wrap domain has
  -- | no pin.
  , wrapBranchData ::
      Int
      -> PProveStep.StepCompileResult
      -> Either String (WrapBranchData mpvMax)
  }

-- | One branch, as the rules carrier stores it: monomorphic closures
-- | over the rank-2 `StepRule` captured at `mkRuleEntry` time, since
-- | PS rejects a record field holding the rule itself.
data RuleEntry
  :: Type
  -> Int
  -> Int
  -> Type
  -> Type
  -> Int
  -> Row (Type -> Type)
  -> Type
data RuleEntry prevsSpec mpv mpvMax valCarrier inputVal outputSize r = RuleEntry
  { compileFns :: RuleCompileFns mpvMax
  , stepProveFn ::
      AdviceHandler r
      -> PProveStep.StepProveContext mpv
      -> PProveStep.StepCompileResult
      -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
           inputVal
           mpv
           valCarrier
      -- Per slot, the cache key of the wrap proof verified there.
      -> Array (Maybe ProofRef)
      -> Effect (Either EvaluationError (PProveStep.StepProveResult outputSize))
  -- | Where each slot's wrap VK comes from, in slot order: a compiled
  -- | slot's key, or `Nothing` for a side-loaded slot.
  , slotVKs :: Vector mpv (Maybe SlotWrapKey)
  }

-- | A `RuleEntry` whose closures capture the given rule and invoke it
-- | through `preComputeStepDomainLog2`, `stepCompile` and
-- | `stepSolveAndProve`.
mkRuleEntry
  :: forall @mpvMax @outputVal @r
       prevsSpec mpv mpvPad outputSize valCarrier
       inputVal inputVar outputVar
       pad unfsTotal digestPlusUnfs compiled
   . CircuitGateConstructor StepField VestaG
  => SlotWidths prevsSpec mpv
  => SlotKinds prevsSpec compiled mpv
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Add mpvPad mpv mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => SlotStatementsCarrier prevsSpec valCarrier
  => PStepRule r prevsSpec inputVal inputVar outputVal outputVar
  -- | The wrap VK source of each compiled slot, in slot order. A
  -- | side-loaded slot takes none.
  -> Vector compiled SlotWrapKey
  -> Effect (RuleEntry prevsSpec mpv mpvMax valCarrier inputVal outputSize r)
mkRuleEntry rule compiledKeys = do
  let
    slotVKs = slotKeysOf (Proxy :: Proxy prevsSpec) compiledKeys
    ctxAt cfg stepNumChunks selfStepDomainLog2s =
      buildStepProveCtx @prevsSpec cfg stepNumChunks
        (reflectType (Proxy :: Proxy mpvMax))
        slotVKs
        selfStepDomainLog2s
  pure $ RuleEntry
    { compileFns:
        { slotWidths:
            Vector.toUnfoldable (map slotWidthInt (slotWidthsOf (Proxy :: Proxy prevsSpec)))
        , preComputeStepDomainLog2: \cfg stepNumChunks selfStepDomainLog2s ->
            PProveStep.preComputeStepDomainLog2
              @prevsSpec
              @outputSize
              @valCarrier
              @inputVal
              @inputVar
              @outputVal
              @outputVar
              @mpvMax
              @mpvPad
              badAdvice
              (ctxAt cfg stepNumChunks selfStepDomainLog2s)
              rule
        , stepCompile: \cfg stepNumChunks selfStepDomainLog2s -> do
            let ctx = ctxAt cfg stepNumChunks selfStepDomainLog2s
            requireSharedStepShifts ctx
            PProveStep.stepCompile
              @prevsSpec
              @outputSize
              @valCarrier
              @inputVal
              @inputVar
              @outputVal
              @outputVar
              @mpvMax
              @mpvPad
              badAdvice
              ctx
              rule
        , wrapBranchData: \selfWrapDomainLog2 result -> do
            pins <- traverse (slotWrapDomainPin selfWrapDomainLog2) slotVKs
            pure
              { mpv: reflectType (Proxy :: Proxy mpv)
              , stepDomainLog2: proverIndexDomainLog2 result.proverIndex
              , stepVK: result.verifierIndex
              , prevWrapDomainPins:
                  Vector.append (Vector.replicate @mpvPad (Just paddingWrapDomain)) pins
              }
        }
    , stepProveFn: \handler ctx compileResult advice prevProofs ->
        PProveStep.stepSolveAndProve
          @prevsSpec
          @outputSize
          @valCarrier
          @inputVal
          @inputVar
          @outputVal
          @outputVar
          @mpvMax
          @mpvPad
          handler
          ctx
          rule
          compileResult
          advice
          prevProofs
    , slotVKs
    }

-- A local name for `StepRuleAt`, to keep the `RuleEntry` field types
-- free of an import cycle.
type PStepRule r prevsSpec inputVal inputVar outputVal outputVar =
  PProveStep.StepRuleAt r prevsSpec inputVal inputVar outputVal outputVar

--------------------------------------------------------------------------------
-- compileMulti — N-branch compile entry point.
--
-- Three stages: each branch's step circuit is compiled on its own, at
-- its own prevs spec and `max_proofs_verified`; one wrap circuit is
-- compiled over all of them; and each branch gets a prover closure
-- that bakes its own index into the wrap statement's `whichBranch`.
--
-- `inputVal` and `outputVal` are shared across the
-- branches, because the wrap VK's public-input layout is the same for
-- every proof under it.
--------------------------------------------------------------------------------

-- | One rule's `StepProveContext`: the shared config combined with
-- | that rule's `slotVKs` and run through `stepProveContextOf` for the
-- | per-slot layout.
buildStepProveCtx
  :: forall @prevsSpec mpv
   . SlotWidths prevsSpec mpv
  => Reflectable mpv Int
  => CompileMultiConfig
  -> Int
  -- ^ the declared `@stepChunks`
  -> Int
  -- ^ the compile's `mpvMax`, which fixes its wrap domain
  -> Vector mpv (Maybe SlotWrapKey)
  -> NonEmptyArray Int
  -> PProveStep.StepProveContext mpv
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
  in
    stepProveContextOf perRuleCfg
      (map slotWidthInt (slotWidthsOf (Proxy :: Proxy prevsSpec)))
      selfStepDomainLog2s

-- | Fails unless each slot's candidate step domains share their
-- | permutation shifts. The step circuit finalizes a slot's previous
-- | proof with one shift set, its first candidate's.
requireSharedStepShifts
  :: forall mpv
   . Reflectable mpv Int
  => PProveStep.StepProveContext mpv
  -> Effect Unit
requireSharedStepShifts ctx =
  forWithIndex_ ctx.srsData.perSlotFopDomainLog2s \slot log2s -> do
    let shifts = domainShifts @StepField (NonEmptyArray.head log2s)
    for_ log2s \log2 ->
      when (domainShifts @StepField log2 /= shifts)
        $ Exc.throw
        $ "compileMulti: the candidate step domains of slot "
            <> show (getFinite slot)
            <> ", log2s "
            <> show (NonEmptyArray.toArray log2s)
            <> ", do not share their permutation shifts"

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
  :: forall @prevsSpec prevsCarrier @mpv @valCarrier
       @inputVal @inputVar @outputVal @outputVar
       @topBranches
       @mpvMax @mpvPad @stepChunks numChunksPred
       branches branchesPred topBranchesPred
       pad unfsTotal digestPlusUnfs outputSize
       padMax totalBasesMax totalBasesMaxPred
       tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
       r
   . SplitPrevs prevsSpec prevsCarrier valCarrier mpv
  => SlotWidths prevsSpec mpv
  => SlotStatementsCarrier prevsSpec valCarrier
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Add 1 branchesPred branches
  -- `topBranches` sizes every branch's step domain log2s, the `Self`
  -- slots' candidates; `branches` is the wrap circuit's per-branch
  -- carrier count. They coincide, but stay separate to match the
  -- rule-level signatures.
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
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => AdviceHandler r
  -> Proxy stepChunks
  -> Int
  -- ^ branchIdx — baked into the wrap statement's `whichBranch`.
  -> CompileMultiConfig
  -> WrapCompileResult
  -> Vector branches (WrapBranchData mpvMax)
  -- ^ the same per-branch vector wrap compile was given, from which
  --   the wrap solver rebuilds the same `WrapMainConfig`
  -> Vector mpvMax (Maybe ProofsVerified)
  -- ^ this branch's wrap-domain pins, padding slots first
  -> Vector topBranches Int
  -- ^ every branch's step domain log2, which gives this rule's
  --   `finalizeOtherProofCircuit` its dispatch table for `Self` slots
  -> PProveStep.StepCompileResult
  -- ^ this branch's step compile result
  -> Int
  -- ^ this branch's selfStepDomainLog2 (from the pre-pass)
  -> RuleEntry prevsSpec mpv mpvMax valCarrier inputVal outputSize r
  -> StepInputs prevsSpec inputVal prevsCarrier
  -> Effect (Either ProveError (CompiledProof mpvMax (StatementIO inputVal outputVal)))
runMultiProverBody
  handler
  ncProxy
  branchIdx
  cfg
  wrapResult
  perBranchVec
  branchPins
  allStepDomainLog2s
  stepCR
  selfStepDomainLog2
  (RuleEntry r)
  { appInput, prevs } = do
  let
    widths = slotWidthsOf (Proxy :: Proxy prevsSpec)
    split = splitPrevs (Proxy :: Proxy prevsSpec) prevs
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
    stepProveCtx = stepProveContextOf perRuleCfg (map slotWidthInt widths)
      (NonEmptyArray.fromFoldable1 allStepDomainLog2s)

  { stepAdvice, challengePolynomialCommitments, baseCaseWrapPublicInputs, prevProofRefs } <-
    mkStepAdvice perRuleCfg stepCR wrapResult appInput widths split.values
      split.slots

  let
    PProveStep.StepAdvice sa = stepAdvice

    proveDataSideInfo =
      { challengePolynomialCommitments
      , unfinalizedSlots: sa.publicUnfinalizedProofs
      , baseCaseWrapPublicInputs
      }
    proveData = shapeProveData perRuleCfg wrapResult proveDataSideInfo
      (Vector.drop @mpvPad branchPins)
      widths
      split.slots

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
      , dummyKimchiPrevEntry:
          { sgX: (unwrap dummyWrapSgInStepField).x
          , sgY: (unwrap dummyWrapSgInStepField).y
          , challenges: dummyIpaChallenges.wrapExpanded
          }
      , dummySlotChal: map F dummyIpaChallenges.wrapExpanded
      }

    proveDataMax = padShapeProveData padDummies wrapResult.slotWidths proveData

  eStepResult <- r.stepProveFn handler stepProveCtx stepCR stepAdvice prevProofRefs
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
              buildWrapMainConfigMulti @branches @mpvMax cfg.srs.vestaSrs
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
              , prevWrapDomainIndices:
                  map (\pv -> F (Curves.fromInt (fromEnum pv) :: WrapField))
                    proveDataMax.prevWrapDomainIndices
              }
          , debug: cfg.debug
          , proofCache: cfg.proofCache
          , step:
              { vkDigest: BigInt.toString (toBigInt (verifierIndexDigest stepCR.verifierIndex))
              , publicInput: piKey stepResult.publicInputs
              }
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
            , widthData
            , stepDomainLog2: selfStepDomainLog2
            }

compileMulti
  :: forall @rs @outputVal @stepChunks numChunksPred
       r
       inputVal mpvMax
       branches
       rulesCarrier
       proversCarrier
       branchesPred totalBases totalBasesPred
       tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5
   . CompilableRulesSpecShape rs inputVal outputVal
       branches
       branches
       mpvMax
       rulesCarrier
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
  => CompileMultiConfig
  -> rulesCarrier
  -> Effect
       ( MultiOutput
           proversCarrier
           branches
           mpvMax
           inputVal
           outputVal
       )
compileMulti cfg rules = do
  let
    ruleFns = ruleCompileFns
      @rs
      @inputVal
      @outputVal
      @branches
      @branches
      @mpvMax
      @rulesCarrier
      @r
      rules
    slotWidths = deriveWrapSlotWidths (reflectType (Proxy :: Proxy mpvMax))
      (Vector.toUnfoldable (map _.slotWidths ruleFns))
  -- Step 1: the per-rule pre-pass, then the per-rule step compiles
  -- against the domains it found.
  { stepResults, log2s } <- runMultiCompileFull cfg
    (reflectType (Proxy :: Proxy stepChunks))
    ruleFns

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
    selfWrapDomainLog2 =
      resolveSelfWrapDomainLog2 (reflectType (Proxy :: Proxy mpvMax)) cfg.wrapDomainOverride
  perBranchVec <- either Exc.throw pure $ sequence $
    Vector.zipWith (\ruleFn result -> ruleFn.wrapBranchData selfWrapDomainLog2 result)
      ruleFns
      stepResults

  -- Step 2: shared wrap compile across all branches.
  wrapResult <- wrapCompile @branches @mpvMax @stepChunks
    { wrapMainConfig:
        buildWrapMainConfigMulti @branches @mpvMax cfg.srs.vestaSrs
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
  -- `Exc.throw`, not `unsafeThrow`: the latter throws as soon as it is
  -- evaluated, which in a strict language is before `when` inspects the
  -- condition.
  when (actualWrapDomainLog2 /= selfWrapDomainLog2)
    $ Exc.throw
    $ "compileMulti: this circuit was compiled for proofs using the wrap "
        <> "domain of size "
        <> show selfWrapDomainLog2
        <> ", but the actual wrap domain size for the circuit has size "
        <> show actualWrapDomainLog2
        <> ". Set wrapDomainOverride to the correct domain size."

  -- Step 3: one prover closure per branch, each capturing its own
  -- index and sharing the step-domain vector.
  provers <- buildBranchProvers
    @rs
    @inputVal
    @outputVal
    @branches
    @branches
    @mpvMax
    @rulesCarrier
    @proversCarrier
    @r
    (Proxy :: Proxy stepChunks)
    0
    cfg
    wrapResult
    perBranchVec
    (map _.prevWrapDomainPins perBranchVec)
    log2s
    stepResults
    rules

  -- Step 4: shared verifier + tag.
  unique <- newUnique
  let
    -- The wrap circuit's own domain log2, checked above against the
    -- circuit that was built. An `External` slot over this system
    -- reads its lagrange basis at this domain.
    wrapDomainLog2 = actualWrapDomainLog2

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
    , tagData:
        { wrapVerifierIndex: wrapResult.verifierIndex
        , wrapDomainLog2
        , stepDomainLog2s:
            NonEmptyArray.nub (NonEmptyArray.fromFoldable1 (map _.stepDomainLog2 perBranchVec))
        , numChunks: reflectType (Proxy :: Proxy stepChunks)
        }
    }
