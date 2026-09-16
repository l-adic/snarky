-- | Per-rule shape machinery: types, the `CompilableSpec` class +
-- | its Nil / Cons instances, and supporting helpers.
-- |
-- | The user-facing `compile` entry point lives in
-- | `Pickles.Prove.CompileMulti` (which dispatches through the class
-- | methods defined here). Mirrors OCaml `Pickles.compile_promise` at
-- | a high level, modulo the advice-monad model difference (PS uses
-- | `CircuitM t m` polymorphism; OCaml dispatches via
-- | request/handler).
-- |
-- | Everything that differs between the empty prev list (`Unit`) and a
-- | `Slot n nc stmt /\ rest` lives inside `CompilableSpec`'s two
-- | instances; `compile` dispatches through them.
module Pickles.Prove.Compile
  ( PrevSlot(..)
  , SlotWrapKey(..)
  , ProverVKs
  , ProveError
  , StepInputs
  , Tag(..)
  , BranchProver(..)
  , RulesSpec
  , RulesNil
  , RulesCons
  , RuleEntry
  , mkRuleEntry
  , compileMulti
  -- Internal classes re-exported because instance resolution at user
  -- call sites needs them in scope. Not directly callable.
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
import JS.BigInt as BigInt
import Pickles.Constants (roughDomainsLog2, zkRowsForNumChunks)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (PointEval, domainGenerator, domainShifts)
import Pickles.PlonkChecks (collapseChunkedEvals, collapsePointEval)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.ProofsVerified (boolVecToProofsVerified)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Slot as RuntimeSlot
import Pickles.Prove.SlotCompile as SlotCompile
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
import Pickles.Sideload.Advice (class MkUnitVkCarrier, class SideloadedVKsCarrier)
import Pickles.Sideload.Bundle (Bundle, SlotProveVk(..), projectVk, requireBundle, verifierIndex) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey(..)) as SLVK
import Pickles.Slots (Slot)
import Pickles.Step.Dummy
  ( baseCaseDummies
  , computeDummySgValues
  , wrapDomainLog2ForProofsVerified
  , wrapDummyUnfinalizedProof
  )
import Pickles.Step.Dummy as Dummy
import Pickles.Step.Main (class BuildSlotVkSources, SlotVkBlueprint)
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier, class StepSlotsTyp)
import Pickles.Step.Types as Step
import Pickles.Types (AllocEvals(..), PaddedLength, PerProofUnfinalized(..), StatementIO(..), StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.Util.Unique (Unique, newUnique)
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
import Pickles.Verify.Types (toPlonkMinimal)
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
  ) as ProofFFI
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

-- | Identity bundle for a Pickles rule emitted by `compile`. Carries:
-- |
-- | * `unique` — opaque runtime token allocated fresh on every
-- |   `compile` call (`Data.Unique`-style). Routing key for downstream
-- |   consumers — `compileFamily`'s VK registry, side-loaded VK
-- |   registries at prove time, or any other lookup-by-rule-identity.
-- |   Two distinct compiles always produce distinct uniques even if
-- |   their type signatures match.
-- |
-- | * `verifier` — the rule's verifier, ready to feed
-- |   `Pickles.verify` and to extract step-side constants from
-- |   (stepDomainLog2, stepEndo, etc.) for InductivePrev's wrap PI
-- |   reconstruction.
-- |
-- | The phantom `(stmt, mpv)` parameters provide structural type
-- | safety — different-shape rules' tags can't be substituted for each
-- | other. Same-shape collisions surface at runtime (mismatched
-- | `unique` → wrong VK in proof). The production prover instantiates
-- | `stmt = StatementIO inputVal outputVal`, so the bundled statement
-- | type discriminates on both the rule's input and output types.
-- |
-- | Mirrors OCaml's `Tag.t` (`pickles/tag.mli`): the `unique` is the
-- | analog of `Type_equal.Id.uid`, the phantom params analog of the
-- | OCaml type parameters.
newtype Tag :: Type -> Int -> Type
newtype Tag stmt mpv = Tag
  { unique :: Unique
  , verifier :: Verifier
  }

derive instance Newtype (Tag stmt mpv) _

-- | VK bundle downstream compiles consume as `perSlotImportedVKs`.
type ProverVKs =
  { stepCompileResult :: StepCompileResult
  , wrapCompileResult :: WrapCompileResult
  , wrapDomainLog2 :: Int
  -- | The imported rule's compile-time `@stepChunks`. Propagated from
  -- | the producer so the consumer (e.g. `mkStepAdvice`'s per-slot
  -- | `External` case) reads the declared value directly instead of
  -- | back-deriving it from the realized step domain log2.
  , stepNumChunks :: Int
  }

-- | Per-slot wrap-key info supplied at compile time. Mirrors the
-- | semantic intent of OCaml `Types_map.For_step.Optional_wrap_key.t`
-- | (`mina/src/lib/crypto/pickles/types_map.mli:103-112`):
-- |
-- |   type 'branches t = 'branches known option
-- |
-- | OCaml encodes the dispatch as `option` because the framework
-- | discriminates self-vs-external slots via runtime `Type_equal.Id
-- | .same_witness self.id tag.id` (`step_main.ml:514-528`). PureScript
-- | exposes the discriminant directly as a sum constructor:
-- |
-- | * `Self` — the slot points at the rule currently being compiled.
-- |   Step compile substitutes the current rule's `dlog_plonk_index`;
-- |   the wrap VK is read from advice (`Req.Wrap_index`) at prove
-- |   time because at step-compile time the wrap circuit hasn't been
-- |   compiled yet.
-- | * `External vks` — the slot points at a previously-compiled
-- |   external rule. The user supplies that rule's `compile` output
-- |   (`{ stepCompileResult, wrapCompileResult, wrapDomainLog2 }`).
-- |   Step compile bakes the external wrap VK as a constant in the
-- |   step circuit (no advice path needed for that slot).
-- | * `SideLoadedKey` — the slot has no compile-time key at all. Its
-- |   wrap VK arrives as a runtime witness in `StepInputs.sideloadedVKs`
-- |   and is allocated in-circuit; what compile time fixes is only the
-- |   upper bound on its `max_proofs_verified`, which the slot's `n`
-- |   carries. OCaml's `Types_map.t` makes the same distinction as a
-- |   runtime sum (`Compiled` / `Side_loaded`).
-- |
-- | This is the only place the compiled/side-loaded distinction is
-- | made. It used to also be a type-level kind index on
-- | `Pickles.Slots.Slot`, which forced every spec-indexed class on this
-- | path into two near-identical instances that then had to narrow this
-- | sum back down to one case each.
data SlotWrapKey
  = Self
  | External ProverVKs
  | SideLoadedKey

type StepInputs :: Type -> Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier vkCarrier =
  { appInput :: inputVal
  , prevs :: prevsCarrier
  -- | Spec-indexed runtime side-loaded VK carrier: one
  -- | `SlotProveVk nc` per slot. A rule whose slots are all compiled
  -- | (NRR/Simple_chain/Tree/TwoPhaseChain) passes `NoSideLoadedVk`
  -- | at every position. A slot whose key is `SideLoadedKey` must be
  -- | given `SideLoadedVk` its runtime bundle here; supplying one for
  -- | a `Self` or `External` slot is refused rather than ignored.
  -- | Mirrors
  -- | OCaml's per-prove `~handler`: the runtime VK is bound at prove
  -- | time, not at compile time.
  , sideloadedVKs :: vkCarrier
  }

-- | Per-slot prev value the user supplies at `prover.step` time.
-- |
-- | * `BasePrev` — no real previous proof yet (proof-level base case,
-- |   e.g. Simple_chain b0). The user supplies a full dummy statement
-- |   (the prev rule's `StatementIO inputVal outputVal`) so the class's
-- |   `mkStepAdvice` can populate the per-slot entry of `prevAppStates`
-- |   in advice. The values are circuit-irrelevant (their slot has
-- |   `proofMustVerify[i] = false`) but must typecheck as the prev
-- |   rule's full statement. Simple_chain's convention is
-- |   `StatementIO { input: F (negate one), output: unit }`.
-- |
-- | * `InductivePrev` — the user has a real previous proof (typically
-- |   returned by a previous `prover.step` call) AND the `Tag` that
-- |   identifies the rule that produced it (carrying the VK + runtime
-- |   `Unique` for routing). For self-recursive rules the tag is the
-- |   same one returned by the current `compile`; for external slots
-- |   (heterogeneous shapes like Tree's NRR slot) it's the tag from
-- |   the prev rule's compile.
-- | The slot's `n` parameter is the proof system's outer
-- | `Max_proofs_verified.n` (= OCaml `'mlmb`), NOT the prev rule's
-- | local width. After the `widthData`-existential refactor of
-- | `CompiledProof`, the prev's actual width is hidden inside
-- | `CompiledProof.widthData`, so the slot's `n` matches uniformly
-- | across all branches' proofs.
data PrevSlot :: Type -> Int -> Type -> Type
data PrevSlot inputVal n stmt
  = BasePrev { dummyStatement :: stmt }
  | InductivePrev
      (CompiledProof n stmt)
      (Tag stmt n)

type CompileConfig :: Int -> Type
type CompileConfig mpv =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -- | Where each slot's wrap VK comes from, in slot order.
  -- |
  -- | A `Vector`, not a nested tuple: `SlotWrapKey` is one
  -- | unparameterised sum, so every position has the same type and a
  -- | tuple chain could express nothing the length does not. It carried
  -- | per-slot types back when `Slot` had a `SlotKind` index; with that
  -- | gone it was `SlotWrapKey` replicated. The length stays in the type
  -- | so a rule that supplies the wrong number of keys is still a type
  -- | error rather than a runtime one.
  , perSlotImportedVKs :: Vector mpv SlotWrapKey
  , debug :: Boolean
  -- | The compile's declared `@stepChunks` (OCaml `compile.ml`'s
  -- | `num_chunks`, one value for every branch). `Self` slots read their
  -- | prev step proof's `zk_rows` from it.
  , stepNumChunks :: Int
  -- | The wrap domain this compile's own wrap circuit is assumed to
  -- | have. One value for the whole compile, so a `Self` prev slot,
  -- | which verifies a proof of this very system, reads it directly
  -- | instead of deriving a domain of its own.
  , selfWrapDomainLog2 :: Int
  -- | Optional disk proof-cache (test/dev). `Nothing` = no caching
  -- | (always prove). Mirrors OCaml `compile`'s `?proof_cache`.
  , proofCache :: Maybe ProofCache
  }

-- | The compile's wrap domain: the override when given, otherwise the
-- | three-entry table applied to `max_proofs_verified`.
-- |
-- | This mirrors OCaml `compile.ml:464-477`, and the mirror is exact in
-- | a way worth recording. `Wrap_domains.Make.f`, the function that
-- | `compile.ml` actually calls, is nothing but that table lookup. The
-- | same functor defines `f_debug`, which builds a dummy wrap circuit
-- | and measures it, but nothing calls it, and the file carries a TODO
-- | asking why the functor ignores its own arguments.
-- |
-- | So neither side estimates. The table is a guess that can be wrong,
-- | which is what the override is for, and what the check after
-- | `wrapCompile` reports when the guess misses.
resolveSelfWrapDomainLog2 :: Int -> Maybe Int -> Int
resolveSelfWrapDomainLog2 mpvMax = case _ of
  Just o -> o
  Nothing -> wrapDomainLog2ForProofsVerified mpvMax

-- | One slot's compile-time key, as the runtime slot record the
-- | per-slot derivations in `Pickles.Prove.Slot` read.
-- |
-- | This is the whole of what the erased `SlotKind` index used to say,
-- | and it says it once.
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

-- | Everything `shapeCompileData` does for one slot: run the slot
-- | compiler over it, splice the four per-slot entries onto the tail,
-- | and set the rule-wide fields.
-- |
-- | `slotNc` stays a type variable: a slot's chunk count belongs to the
-- | compile that produced its previous proofs, so two slots of one rule
-- | can differ. That is what keeps the carrier a typed chain and this a
-- | helper rather than a fold over an array.
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
  headEntry = SlotCompile.slotCompileEntry
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

-- | What one slot contributes to the step prover's advice, spliced onto
-- | the tail.
-- |
-- | Third of the three shared bodies, and the one that touches the
-- | typed carriers. It never inspects them: it conses this slot's
-- | statement onto the tail's statement chain and this slot's key cell
-- | onto the tail's key chain, both of which stay exactly as typed as
-- | they were. That is why the statements can remain typed while the
-- | body around them is shared.
-- |
-- | The recursive call arrives as an unforced `Effect` so that this
-- | slot's oracle work still happens before the tail's, as it did when
-- | the body lived in the instance.
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
      -- Wrap VK is compile-wide-constant; propagate the base case's
      -- unchanged. Value-identical to a fresh extraction from the same
      -- wrap result.
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
            -- branch_data.domain_log2 of the prev's wrap statement holds
            -- the prev's step domain (per OCaml
            -- `Wrap_deferred_values.expand_deferred`'s use of
            -- `Branch_data.domain branch_data` for `step_domain`).
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
        -- width-erased, with the constants it is judged against, and the
        -- existential opened once here rather than around this whole
        -- block. See `Pickles.Verify.PrevProofData`.
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

        -- The prev's branch-specific step domain. The `Verifier` no
        -- longer carries a step domain log2 (it's per-branch); use the
        -- proof's own `stepDomainLog2` so multi-branch dispatch picks
        -- the right domain for each prev. Mirrors OCaml
        -- `branch_data.domain_log2` driving `step_domain` inside
        -- `expand_deferred`.
        prevStepGenerator = domainGenerator prevData.proof.stepDomainLog2

        prevStepShifts = domainShifts prevData.proof.stepDomainLog2

        prevVanishesOnZk = ProofFFI.permutationVanishingPolynomial
          { domainLog2: prevData.proof.stepDomainLog2
          , zkRows: prevVerifier.stepZkRows
          , pt: prevZetaField
          }

        -- The unpadded accumulators, reified back to a `Vector n`.
        -- `expandDeferredForVerify` is `forall n` and folds over them,
        -- so the length must be the proof's real width: padding here
        -- would change both the challenges digest and the combined
        -- inner product.
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

-- | What one slot contributes to the wrap prover's inputs, spliced onto
-- | the tail.
-- |
-- | As with `consShapeCompileData`, the two instances ran the same body
-- | and differed only in a handful of values, which are the
-- | `slotParams` argument: where the slot's wrap verifier index comes
-- | from, what its wrap domain is, its own width, and the padding that
-- | width implies. A compiled slot resolves the first two from the
-- | enclosing compile or an imported one; a side-loaded slot reads them
-- | off the runtime key.
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
  -- Wrap-domain index is `wrap_domain_log2 - 13` per the
  -- `allPossibleDomainLog2s = [13, 14, 15]` table in
  -- `Pickles.Prove.Wrap`.
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
  -- Slot-specific dummies sized by the slot's own width, not the
  -- enclosing rule's. Matters for Tree-style heterogeneous slots: slot
  -- 0 (NRR, width 0) uses width-0 dummies, slot 1 (Self, width 2) uses
  -- width-2 dummies.
  bcd = Dummy.baseCaseDummies { maxProofsVerified: slotParams.slotWidth }
  dummySgs = Dummy.computeDummySgValues bcd srs.pallasSrs srs.vestaSrs
  stepSgD = dummySgs.ipa.step.sg -- AffinePoint WrapField

  { head: PerProofUnfinalized headUnfRaw, tail: _ } =
    Vector.uncons sideInfo.unfinalizedSlots
  { head: headChalPolyComm, tail: _ } =
    Vector.uncons sideInfo.challengePolynomialCommitments
  { head: headBaseCaseWrapPI, tail: _ } =
    Vector.uncons sideInfo.baseCaseWrapPublicInputs

  -- Type1→Type2 cross-field coerce of the raw step-advice unfinalized
  -- entry into the wrap-advice shape (`Type2 (F WrapField)`).
  -- Field-by-field per B0Producer:353-368.
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
        -- Digest.Constant cross-field coerce (step→wrap). Protocol-
        -- level, matches OCaml's limb packing.
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

  -- msgForNextWrap real challenges, computed by endo-expanding the head
  -- slot's raw bp challenges via the wrap endo scalar.
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
        -- `dummyWrapProof` is a WRAP proof: its publicEvals chunk count
        -- is Dim 2 (`WrapVkChunks`), pinned to 1 (wrap domain ≤ wrap
        -- SRS — same invariant as `num_chunks_by_default`). The
        -- dummy wrap proof's public eval = the oracle's recomputed
        -- x_hat (OCaml `wrap.ml:110-116` `None` branch), NOT
        -- `proofData(dummy).evals.public` — the dummy wire proof
        -- carries `evals.public = None`, which decodes to a
        -- placeholder. Run the oracle on the dummy with its wrap PI +
        -- base-case dummy prev-challenges (the same inputs the step
        -- finalize uses); mirrors the InductivePrev oracle below.
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

        -- As in `mkStepAdvice`: the erased proof plus its constants,
        -- existential opened once. This branch needs only the padded
        -- accumulators, so there is no unpadded vector to reify and no
        -- raw record to keep.
        prevData = prevProofDataOf prevVerifier prevCp

        prevStepBpChalsExpanded =
          map
            ( \sc ->
                toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                  stepEndoScalarF
            )
            prevData.proof.rawBulletproofChallenges

        prevWrapPI = wrapPublicInputVP prevVerifier prevData.proof

        -- FFI boundary: kimchi's `prev_challenges` argument expects a
        -- flat `Array {sgX, sgY, challenges :: Array}` of length
        -- PaddedLength=2. Build it from the pre-padded Vectors via
        -- `Vector.zipWith`, then convert to Array exactly once at the
        -- boundary. (sgX/sgY are `Vesta.ScalarField = StepField` — the
        -- Pallas point's coords live in Pallas's base field, which
        -- equals Vesta's scalar field.)
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

-- | Shape-constant compile-time data, provided by the `CompilableSpec`
-- | instance. Everything here is derived from the `prevsSpec` shape +
-- | the `perSlotImportedVKs` bundle — no dependence on the rule or on
-- | per-proof appInput/prevs.
-- |
-- | * `stepProveCtx` — step solver's context; `srsData`'s per-slot
-- |   vectors are shape-dependent (empty for Nil, populated from VKs
-- |   for Cons).
-- | * `wrapDomainLog2` — OCaml `wrap_domains.h` (13 for N=0 in pickles,
-- |   14 for N=1, 15 for N=2).
type ShapeCompileData :: Int -> Int -> Type -> Type
type ShapeCompileData mpv nd blueprints =
  { stepProveCtx :: StepProveContext mpv nd blueprints
  , wrapDomainLog2 :: Int
  }

-- | Side info from `mkStepAdvice`'s return that `shapeProveData` needs.
-- |
-- | * `challengePolynomialCommitments` — per-slot outer step-proof
-- |   opening sgs; feeds each slot's kimchi-prev real entry. For Cons1
-- |   (Simple_chain) this is a singleton vector; for multi-slot
-- |   (Tree) one entry per slot.
-- | * `unfinalizedSlots` — per-slot step-field unfinalized proofs,
-- |   Type1→Type2 coerced in `shapeProveData` to build
-- |   `prevUnfinalizedProofs`.
-- | * `baseCaseWrapPublicInputs` — per-slot serialized
-- |   `dummyWrapTockPublicInput` arrays, passed to `proofOraclesRec`
-- |   so `shapeProveData`'s `dummyWrapXhat` evals match what the step
-- |   circuit sees. Per-slot because Tree's heterogeneous slots have
-- |   distinct prev-rule wrap statements with distinct serializations.
-- |
-- | For recursion: each Cons level extracts the head entry via
-- | `Vector.head` and calls `shapeProveData @rest` with the tails
-- | (`Vector.tail`) of all per-slot vectors.
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

-- | All shape-specific per-slot data needed at wrap-stage construction.
-- | Fields are Vector mpv (one entry per slot); `runMultiProverBody`
-- | pads the mpv-sized vectors to wrap-hack Vector 2 where needed and
-- | computes the proofs-verified mask from `mpv` directly.
-- |
-- | Nil provides empty vectors (Vector.nil for everything, noSlots for
-- | `slotsValue`). Cons recursively cons each slot's entry onto the
-- | tail from `shapeProveData @rest`.
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
  -- | Runtime realisation of the `slots` type constructor carrying
  -- | each prev's wrap bp-challenges.
  , slotsValue :: Array (Array (Vector WrapIPARounds (F WrapField)))
  }

--------------------------------------------------------------------------------
-- padShapeProveData — convert ShapeProveData mpv → ShapeProveData
-- mpvMax. Mirrors the rule's actual mpv shape (driven by prevsSpec) up
-- to the wrap circuit's wider mpvMax.
--------------------------------------------------------------------------------

-- | Per-entry dummy values for padding. Each field is one entry's
-- | worth — `padShapeProveData` front-pads each
-- | `Vector mpv` field with `(mpvMax - mpv)` copies of the
-- | corresponding dummy.
-- |
-- | Constructed by the caller (`runMultiProverBody`) from the wrap
-- | circuit's `mpvMax`-sized `BaseCaseDummies` + SRS-derived sg
-- | values. Mirrors OCaml `step.ml:736-770`'s `extend_front` calls
-- | which use `Unfinalized.dummy`, dummy `Wrap_proof_state`, and
-- | dummy IPA challenges.
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
-- | front-padding each `Vector mpv` field with `mpvPad = mpvMax - mpv`
-- | copies of the corresponding dummy. Mirrors OCaml
-- | `step.ml:736-770`'s `extend_front unfinalized_proofs ...
-- | Unfinalized.dummy` and the analogous padding for the other
-- | per-prev fields.
-- |
-- | A single-rule caller has `mpv = mpvMax`, hence `mpvPad = 0`, and
-- | every `Vector.replicate @0` below is empty and every append the
-- | identity — so that case needs no branch of its own. It used to
-- | have one: an identity instance ahead of this body in an `else`
-- | chain, there to keep the solver from being asked for
-- | `Add 0 mpv mpv`. It answers.
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
  -- ones. Was `convertSlots`, which needed a class instance per pair
  -- of carrier shapes and only ever had two.
  --
  -- Each dummy slot is as wide as the slot the wrap circuit allocated
  -- for it: `Wrap.Main` allocates `oldBpChals` through
  -- `perSlotTyp widths`, whose size is `sum widths`, and `existsTyp`
  -- assigns from the value's fields. A dummy narrower than its slot
  -- leaves the tail variables allocated and unassigned, which the
  -- solver reports as `MissingVariable` from inside `b-poly`.
  , slotsValue:
      map (\w -> Array.replicate w dummies.dummySlotChal)
        (Array.take (reflectType (Proxy @mpvPad)) slotWidths)
        <> sd.slotsValue
  }

--------------------------------------------------------------------------------
-- CompilableSpec — the shape-dependent dispatch class
--------------------------------------------------------------------------------

-- | Shape-specific data provider. Instances provide small per-shape
-- | method bodies; the full compile flow (`runCompile`, below) is
-- | a single top-level polymorphic function that dispatches through
-- | these methods.
-- |
-- | Fundeps `prevsSpec -> prevsCarrier mpv` mean the user only pins
-- | `prevsSpec`; the other axes are derived.
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
  -- | Compile-time shape data (stepProveCtx, constants). Nil: empty
  -- | per-slot vectors + wrapDomainLog2=13 + noSlots.
  -- | Cons: populated from `perSlotImportedVKs` + `wrapDomainLog2`
  -- | for its mpv.
  -- |
  -- | The `selfStepDomainLog2` parameter is the rule's own step-circuit
  -- | domain log2 — used as `slotFopDomainLog2` for `Self` slots (the
  -- | slot's prev = the rule itself, recursing). At pre-pass time
  -- | (gate-counting only) callers pass `20` (= OCaml `rough_domains`)
  -- | as a placeholder; the real `compile` call passes the value
  -- | computed by the pre-pass. `External` slots ignore this argument
  -- | and read the imported rule's step domain from its prover index.
  -- | The `selfStepDomainLog2s :: Vector nd Int` parameter is the
  -- | (deduped) Vector of all step-domain log2s the slot's source
  -- | proof system could have. For single-rule callers it's
  -- | `Vector 1 [theLog2]`; for multi-rule (CompileMulti) it's
  -- | `Vector branches [...]`. Used to populate
  -- | `srsData.perSlotFopDomainLog2s` for `Self` slots.
  -- | `External` slots ignore this argument and read the imported
  -- | rule's step domain from its prover index (Vector 1 of that).
  shapeCompileData
    :: forall @nd ndPred
     . Add 1 ndPred nd
    => Compare 0 nd LT
    => Reflectable nd Int
    => CompileConfig mpv
    -> Vector nd Int
    -> ShapeCompileData mpv nd blueprints

  -- | Step solver advice + side info. Recurses on `rest` to assemble
  -- | the multi-slot StepAdvice (PS analog of OCaml `step.ml:736-770`).
  -- |
  -- | `carrier` is class-level (not method-forall'd) so the instance
  -- | body's combined StepAdvice's `perProofSlotsCarrier` (with type
  -- | derived from instance head free vars) unifies with the method's
  -- | return type.
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

  -- | Per-slot wrap-stage data. Recursive: cons head slot's entries
  -- | onto `shapeProveData @rest` output. Takes the outer rule's
  -- | step-advice side info (`challengePolynomialCommitments`,
  -- | publicUnfinalizedProofs)
  -- | for fields that depend on it.
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
    -- | Ro-derived `Dummy.Ipa.Wrap.sg`. Unused at N=0 (no `verify_one`)
    -- | but required by `stepCompile` as the sg_old padding constant.
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
        -- Nil has no prev slots, so `stepDomainLog2` is dead — the
        -- per-slot dummy that consumes it gets replicated to a
        -- `Vector 0` (= empty). `0` is a sentinel; any value works.
        -- `WrapVkChunks` enters `StepAdvice` only via the
        -- `wrapVerifierIndex` field, which `over StepAdvice` rewrites
        -- here to `extractWrapVKCommsAdvice`'s; `buildStepAdvice`'s
        -- dummy wrap-VK is discarded.
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
        -- Nil has no prev slots; per-slot side info is empty.
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

-- | Recursive instance covering all `Slot n nc stmt /\ rest` shapes.
-- | Derives `mpv` and `prevsCarrier` by recursing through `rest`.
-- |
-- | One instance for all three slot sources. Which source a slot has is
-- | the runtime `SlotWrapKey` in `cfg.perSlotImportedVKs`, and the two
-- | methods that read prove-time values dispatch on it. There used to
-- | be two instances, one per `SlotKind`, structurally identical apart
-- | from having that dispatch resolved statically — and each then had
-- | to narrow the runtime blueprint sum back down to its own case, with
-- | an `unsafeThrow` for the case its kind had ruled out.
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
    -- What the prove call supplies for this slot's wrap VK:
    -- `SideLoadedVk bundle` for a side-loaded slot, `NoSideLoadedVk`
    -- for a compiled one, whose key is a compile-time constant.
    -- Mirrors `Pickles.Sideload.Advice.SideloadedVKsCarrier`.
    (SideloadBundle.SlotProveVk WrapVkChunks /\ restVkCarrier)
    -- Compile-time blueprint for this slot's wrap-VK source, one
    -- constructor per source. Bundled into the post-walk
    -- `SlotVkSource` by `buildSlotVkSources` at circuit-build time.
    (SlotVkBlueprint WrapVkChunks /\ restScaffolds)
  where
  shapeCompileData cfg selfStepDomainLog2s =
    consShapeCompileData cfg selfStepDomainLog2s headSlot
      (shapeCompileData @rest restCfg selfStepDomainLog2s)
    where
    { head: headSlotWrapKey, tail: restSlotVKs } = Vector.uncons cfg.perSlotImportedVKs
    restCfg = cfg { perSlotImportedVKs = restSlotVKs }

    -- This slot, as runtime data. The per-slot derivations (wrap
    -- domain, source step domains, zk_rows, VK blueprint) live in
    -- `Pickles.Prove.SlotCompile`; this instance only says what the
    -- slot *is*.
    headSlot :: RuntimeSlot.Slot
    headSlot = runtimeSlotOf (reflectType (Proxy @n)) headSlotWrapKey

  mkStepAdvice cfg stepCR wrapCR appInput (headSlot /\ restPrevs) (headVk /\ restVkCarrier) =
    consMkStepAdvice @n cfg.srs appInput slotParams headVk headSlot
      (mkStepAdvice @rest restCfg stepCR wrapCR appInput restPrevs restVkCarrier)
    where
    { head: headSlotWrapKey, tail: restSlotVKs } = Vector.uncons cfg.perSlotImportedVKs
    restCfg = cfg { perSlotImportedVKs = restSlotVKs }

    -- Same record `shapeCompileData` builds; the derivations below read
    -- it through `Pickles.Prove.Slot` rather than re-deciding the
    -- slot's source once per value.
    runtimeSlot :: RuntimeSlot.Slot
    runtimeSlot = runtimeSlotOf (reflectType (Proxy @n)) headSlotWrapKey

    -- A side-loaded slot's wrap VK is a runtime witness, so its three
    -- domain-ish values come off the bundle rather than off anything
    -- this compile knows. The witness is still sized at the tag's
    -- compile-time upper bound `n`; the runtime key's smaller
    -- `actualWrapDomainSize` is masked in-circuit.
    slotParams = case headSlotWrapKey of
      SideLoadedKey ->
        { slotWrapVK: SideloadBundle.verifierIndex bundle
        , slotWrapDomainLog2: bundleWrapDomainLog2 bundle
        , slotStepDomainLog2:
            -- Side-loaded VKs don't carry the prev's step domain; the
            -- step circuit dispatches via Pseudo over [0..16] in
            -- `Step.FinalizeOtherProof`'s SideLoadedMode. This stand-in
            -- is consumed only at the BasePrev site, where
            -- `proofMustVerify = false` masks its downstream effect;
            -- InductivePrev reads the prev's own `stepDomainLog2`.
            Dummy.wrapDomainLog2ForProofsVerified (reflectType (Proxy @n))
        -- Side-loaded inner proofs in current pickles are universally
        -- `num_chunks_by_default = 1`, so step zk_rows = 3. (The
        -- `side_loaded_domain` Pseudo varies the domain log2, not nc.)
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
        -- `Self`'s prev step circuit is the outer rule itself, so its
        -- num_chunks is the compile-wide declared `@stepChunks`;
        -- `External` reads the imported rule's. Wrap is universally
        -- nc=1 (`num_chunks_by_default`).
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
-- Mirrors `Pickles.Step.Slots.PrevsSpec` (which encodes a per-prev-slot
-- HList) but at the rules level. Each `RulesCons` slot carries the
-- four type-level facts about that branch's rule:
--
--   1. `mpv`         — that branch's `max_proofs_verified`.
--   2. `valCarrier`  — heterogeneous tuple of prev statement types
--                      for THAT branch's prev slots.
--   3. `prevsSpec`   — that branch's prevs HList (in the existing
--                      `PrevsSpec` kind).
--
-- A fourth parameter used to carry the branch's per-slot imported-VK
-- carrier. It was a tuple chain of `SlotWrapKey` repeated, which said
-- nothing its own length did not, and the length is `mpv`. The keys are
-- a `Vector mpv SlotWrapKey` value now. It meant something when `Slot`
-- had a `SlotKind` index and the cells differed per slot.
--
-- All three vary per-branch. The shared types — `inputVal`, `outputVal`,
-- `prevInputVal` — live at the multi-branch level (they parameterize
-- the SHARED wrap VK's public-input layout), not in `RulesSpec`.
--------------------------------------------------------------------------------

-- | Kind: a type-level list of rule specs.
data RulesSpec

-- | Empty rules list. A multi-branch compile with `RulesNil` is
-- | structurally a no-op and is rejected at the API level (no
-- | `CompilableRulesSpecShape` instance for the empty list).
foreign import data RulesNil :: RulesSpec

-- | One branch's contribution to the rules list. The three type-level
-- | parameters bind that branch's mpv / valCarrier / prevsSpec; the
-- | fourth is the rest of the list.
foreign import data RulesCons :: Int -> Type -> Type -> RulesSpec -> RulesSpec

-- | A rule's per-slot `max_proofs_verified`, in slot order.
-- |
-- | `Slot n _ _` already records `n` — that is what its first parameter
-- | is. This reads it back as a value, so the wrap circuit's slot widths
-- | are derived from the spec rather than restated beside it.
class SlotWidths (prevsSpec :: Type) where
  slotWidthsOf :: forall proxy. proxy prevsSpec -> Array Int

instance SlotWidths Unit where
  slotWidthsOf _ = []

instance (Reflectable n Int, SlotWidths rest) => SlotWidths (Slot n stmt /\ rest) where
  slotWidthsOf _ = Array.cons (reflectType (Proxy @n)) (slotWidthsOf (Proxy @rest))

-- | The wrap circuit's per-slot widths, overlaid from every branch's own
-- | slot list.
-- |
-- | A branch with `mpv` slots is front-padded into the last `mpv`
-- | positions of the wrap circuit's `mpvMax`, so two branches can reach
-- | the same position and must agree on its width there — a real slot
-- | supplies exactly `n` challenge stacks (`Add slotPad n PaddedLength`),
-- | and the circuit allocates exactly `widths[i]`. `mpvMax` is a maximum
-- | over branches, so some branch covers every position and the result
-- | is total.
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

-- | `MaxOfRulesMpvs rules mpvMax` enforces `mpvMax = max(ruleMpv across
-- | rules)` at the type level — strict equality, not just `≥`. The
-- | per-rule `Add mpvPad ruleMpv mpvMax` constraint inside
-- | `CompilableRulesSpecShape` already requires `ruleMpv ≤ mpvMax`,
-- | but doesn't pin `mpvMax` to the actual maximum. Threading
-- | `MaxOfRulesMpvs` alongside CompilableRulesSpecShape closes that
-- | gap: any `RulesSpec` uniquely determines its `mpvMax`, so two
-- | call sites that derive `mpvMax` from the same `rules` cannot
-- | disagree.
-- |
-- | Mirrors OCaml's `compile_promise` behavior, which derives
-- | `mpvMax` from the `~max_proofs_verified:(module Nat.NX)`
-- | argument that itself is `max` over each rule's prev count.
class MaxOfRulesMpvs (rules :: RulesSpec) (mpvMax :: Int) | rules -> mpvMax

instance MaxOfRulesMpvs RulesNil 0

instance
  ( MaxOfRulesMpvs rest restMax
  , IntMax ruleMpv restMax mpvMax
  ) =>
  MaxOfRulesMpvs (RulesCons ruleMpv valCarrier prevsSpec rest) mpvMax

-- | Multi-branch compile config. Shape is shared across all branches;
-- | per-branch data lives in the value-level `rulesCarrier` argument
-- | passed alongside (a `Tuple` chain matching the `RulesSpec` shape).
type CompileMultiConfig =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , debug :: Boolean
  , wrapDomainOverride :: Maybe Int
  -- | Optional disk proof-cache (test/dev). `Nothing` = no caching
  -- | (always prove). Mirrors OCaml `compile`'s `?proof_cache`.
  , proofCache :: Maybe ProofCache
  -- | Optional on-disk Lagrange-basis cache. When `Just`, compile warms each
  -- | of the program's real domains (step domains on vesta, wrap domain on
  -- | pallas) through it before any constraint building — so each basis is
  -- | FFT'd once ever and injected from disk thereafter, and the warmed `CRS`
  -- | (shared by reference into prove) needs no recompute. `Nothing` = the SRS
  -- | is used as-is (kimchi computes bases lazily in-process, not persisted).
  , lagrangeCache :: Maybe LagrangeCache
  }

-- | Per-branch prover for ONE branch. Each `RulesCons` slot in the
-- | carrier corresponds to a `BranchProver` of that branch's shape.
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> Type -> Row (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier vkCarrier inputVal outputVal r =
  BranchProver
    ( AdviceHandler r
      -> StepInputs prevsSpec inputVal prevsCarrier vkCarrier
      -> Effect (Either ProveError (CompiledProof mpv (StatementIO inputVal outputVal)))
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
  -- | The compile's declared `@stepChunks`. Propagated so consumers
  -- | constructing `ProverVKs` for an `External` slot can read the
  -- | imported rule's nc without back-deriving it from the step
  -- | circuit's realized domain log2.
  , stepChunks :: Int
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
  , tag :: Tag (StatementIO inputVal outputVal) mpvMax
  , verifier :: Verifier
  , vks :: MultiVKs perBranchStepCarrier
  -- | Per-branch `ProverVKs` handles, in case the caller wants to
  -- | reference an individual branch from a different proof system
  -- | via `External` (e.g., blockchain_snark referencing a specific
  -- | branch of transaction_snark).
  , perBranchVKs :: perBranchVKsCarrier
  }

--------------------------------------------------------------------------------
-- CompilableRulesSpec
--
-- Mirror of `Pickles.Step.Slots.StepSlotsCarrier` at the rules level
-- (one level up from per-prev-slot). Drives multi-branch compile via
-- per-rule dispatch.
--
-- Why class-method dispatch (vs. tuple-stored rules): PS rejects
-- record fields holding `StepRule`'s rank-2 forall. Class-method
-- dispatch sidesteps this — each instance is monomorphic, so the
-- user's rank-2 rule value gets *used* inside the method body
-- (calling `stepCompile` / `stepSolveAndProve`) without ever being
-- *stored* as a record value.
--
-- The funDep `rs -> branches mpvMax` says: the type-level rules spec
-- determines (a) the branch count and (b) the max mpv across rules.
-- The `Add restBranches 1 branches` recurrence computes `branches`
-- at the type level.
--------------------------------------------------------------------------------

-- | `topBranches` is the FIXED outer-compile branch count that flows
-- | UNCHANGED through every recursive instance of this class. It is
-- | distinct from `branches` (the shrinking count of the `rs`-tail at
-- | recursion depth k). The split mirrors OCaml's
-- | `compile.ml:533-568` where `'branches` is a single GADT-scoped
-- | type variable (= `topBranches` here) and the per-branch
-- | `H4.T(Branch_data).t` recursion walks element existentials
-- | without touching `'branches`.
-- |
-- | `topBranches` is what `RuleEntry`'s `nd` parameter binds to, so
-- | each rule's `preComputeStepDomainLog2Fn` / `stepCompileFn` /
-- | `stepProveFn` see a `StepProveContext mpv topBranches` — i.e. a
-- | per-rule context whose multi-domain Pseudo dispatch ranges over
-- | the FULL `topBranches`-sized Vector of step-domain log2s.
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
  -- | Count branches by structural recursion. Validates that
  -- | `branches` is correctly derived as a function of `rs` and that
  -- | the recurrence relation discharges (Cons case adds 1 to the
  -- | rest's count). Returns the same value `Reflectable branches`
  -- | would, but via direct class-method dispatch.
  branchCount :: forall proxy. proxy rs -> Int

  -- | Each branch's own slot widths, in branch order, read off its
  -- | `Slot n _ _` chain. `deriveWrapSlotWidths` overlays these into the
  -- | wrap circuit's single `mpvMax`-long list.
  ruleSlotWidths :: forall proxy. proxy rs -> Array (Array Int)

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
  -- | `StepProveContext mpv` (one per rule) plus the rules carrier;
  -- | sequences each entry's `stepCompileFn ctx` and returns a Tuple
  -- | chain of `StepCompileResult`s in branch order.
  runStepCompiles
    :: AdviceHandler r
    -> perBranchCtxsCarrier
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

  -- | Symmetric to `extractStepCompileFns`: pull each entry's
  -- | `stepProveFn` into a Tuple chain. The per-branch thunk type:
  -- |
  -- |   StepProveContext mpv
  -- |   -> StepCompileResult
  -- |   -> StepAdvice prevsSpec _ _ inputVal mpv carrier valCarrier
  -- |   -> Run (EXCEPT EvaluationError + EFFECT + r) (StepProveResult outputSize)
  -- |
  -- | Used by `buildBranchProvers` to assemble per-branch
  -- | `BranchProver` closures by composing each branch's
  -- | `stepSolveAndProve` with the shared wrap solve+prove flow.
  extractStepProveFns :: rulesCarrier -> stepProveFnsCarrier

  -- | Convert the per-branch `StepCompileResult` Tuple chain into the
  -- | `Vector branches { mpv, stepDomainLog2, stepVK }` shape that
  -- | `buildWrapMainConfigMulti` expects.
  -- |
  -- | For each branch:
  -- |   * `mpv` — reflected from the rule's type-level mpv (each Cons
  -- |     instance has `Reflectable ruleMpv Int`).
  -- |   * `stepDomainLog2` — extracted from the proverIndex via
  -- |     `proverIndexDomainLog2`.
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

-- | Nil instance is polymorphic in `slotsMax` and `topBranches` — Nil
-- | returns unit-shaped carriers regardless of either.
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

-- | Cons instance: per-rule branch increments the running count via
-- | `Add restBranches 1 branches`. The Tuple carrier shape is pinned
-- | by `StepSlotsCarrier prevsSpec … carrier` (carrier from prevsSpec) and
-- | by Add chains (outputSize from mpv). These constraints feed back
-- | into the funDep `rs -> rulesCarrier` resolution.
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
  -- outputSize derives from mpvMax (the wrap circuit's max), not the
  -- rule's mpv: step PI is mpvMax-shaped (mirrors OCaml
  -- step.ml:783-787).
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , Reflectable ruleMpv Int
  -- The spec-derived runtime side-loaded VK carrier; pinned by the
  -- `SideloadedVKsCarrier` fundep `prevsSpec -> vkCarrier`. Threaded
  -- into both the `RuleEntry` and the closure-argument `StepAdvice`
  -- so they reference the same carrier.
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
-- A separate class from `CompilableRulesSpec` because the structural
-- class must NOT carry a `CompilableSpec` super-constraint on its Cons
-- instance: PS can't always discharge it at call sites, and the failure
-- cascades through the funDep chain and leaves all class params
-- unresolved. Splitting lets the structural methods stay light while
-- callers of the shape-data methods opt in to the heavier discharge
-- requirement.
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
  -- | Pre-pass: walk the rules carrier collecting each rule's
  -- | `selfStepDomainLog2` into a `Vector branches Int` (the per-
  -- | recursion-level count). Each rule's `preComputeStepDomainLog2Fn`
  -- | is invoked with a placeholder `StepProveContext` built from the
  -- | supplied `Vector topBranches Int` placeholder (caller passes
  -- | `Vector.replicate roughDomainsLog2`, matching OCaml
  -- | `Fix_domains.rough_domains`).
  -- |
  -- | Mirrors OCaml `compile.ml:533-547`'s pre-pass over branches
  -- | producing `step_domains : (Domains.t, 'branches) Vector.t
  -- | Promise.t`. At the top-level call `branches = topBranches`, so
  -- | the result is a `Vector topBranches Int` of the FULL multi-
  -- | domain vector — the analog of `promise_all step_domains`.
  prePassDomainLog2s
    :: AdviceHandler r
    -> CompileMultiConfig
    -> Int
    -- ^ the declared `@stepChunks`
    -> Vector topBranches Int
    -> rulesCarrier
    -> Effect (Vector branches Int)

  -- | High-level per-branch compile with caller-supplied multi-domain
  -- | `Vector topBranches Int`. The SAME Vector is fed to every
  -- | rule's `stepCompileFn` via `buildStepProveCtx`. Mirrors OCaml
  -- | `compile.ml:568`'s `b.main ~step_domains:all_step_domains` —
  -- | the FULL Vector across all branches lands in every branch's
  -- | step_main call.
  runMultiCompile
    :: AdviceHandler r
    -> CompileMultiConfig
    -> Int
    -- ^ the declared `@stepChunks`
    -> Vector topBranches Int
    -> rulesCarrier
    -> Effect perBranchStepCompileResults

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
  -- |   * `allStepDomainLog2s` — full `Vector topBranches Int`,
  -- |     same for every branch's prover closure (passed unchanged
  -- |     down the recursion). Used at prove time inside
  -- |     `runMultiProverBody` to build the per-rule
  -- |     `StepProveContext` via `buildStepProveCtx`.
  -- |   * step results / rules carriers — per-branch Tuple
  -- |     chains walked in sync with the recursion.
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

-- | Top-level orchestrator: pre-pass + real-pass per-branch step
-- | compile. Constraint `branches ~ topBranches` is achieved by
-- | passing the SAME type variable for both class params at the
-- | call site — at the user's outer call, the recursion's local
-- | `branches` count equals the fixed `topBranches`.
-- |
-- | Inside the class instance recursion, `topBranches` stays fixed
-- | while `branches` shrinks; the recursion still works because
-- | `prePassDomainLog2s` returns `Vector branches Int` (which grows
-- | via `:<` from Nil's `Vector.nil` up to `Vector topBranches Int`
-- | at the outermost call).
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
  -- Lazy, persistent Lagrange-basis warming (opt-in via `lagrangeCache`). The
  -- pre-pass has now yielded the real per-branch step domains, and we are still
  -- before any constraint building (which is what fires the lazy
  -- `mkConstLagrangeBaseLookup` reads). The warmed CRS is shared by reference
  -- into prove, so the prover finds every basis already present — no recompute,
  -- and persisted.
  --
  --   * vesta @ the program's real step domains (from the pre-pass) — the
  --     expensive/large side, kept precise (includes chunked domains > the SRS).
  --   * pallas @ the COMPLETE legal wrap-domain set {13,14,15}. A program's own
  --     wrap domain and every slot's verified-proof wrap domain — Self (= own),
  --     External (an imported VK's domain), SideLoaded (a runtime VK's domain) —
  --     are all in this set, so warming it covers them exhaustively with no slot
  --     inspection. This is exhaustive, not a guess: 13/14/15 are the only wrap
  --     domains (`wrapDomainLog2ForProofsVerified`, mpv 0/1/2). Cheap — three
  --     small 2^15-SRS bases; a Self-only program warms at most two it won't use.
  for_ cfg.lagrangeCache \cache -> do
    -- `warmer` fingerprints each SRS once, then warms each domain under that
    -- fingerprint (cache hit → inject, miss → FFT + store).
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

-- | Nil shape instance is polymorphic in `slotsMax` and `topBranches`
-- | (parallels the structural Nil instance).
-- |
-- | `prePassDomainLog2s` returns `Vector.nil` (= the per-recursion-
-- | level count `branches = 0` here). At the top-level user call,
-- | `branches = topBranches`, so this is only reached when the user
-- | called with empty rs.
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
  -- outputSize derives from mpvMax (the wrap circuit's max).
  , Reflectable mpvPad Int
  , Add mpvPad ruleMpv mpvMax
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  -- Wrap-stage constraints on `mpvMax` (the wrap circuit's wider
  -- shape). `padShapeProveData` front-pads the per-rule `ruleMpv`
  -- shape up to `mpvMax`.
  , Reflectable mpvMax Int
  , Reflectable padMax Int
  , Add padMax mpvMax PaddedLength
  , Compare mpvMax 3 LT
  -- `topBranches` stays fixed across the recursion; required by
  -- `buildStepProveCtx` and Vector dispatch.
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
  -- `Vector.cons` (`(:<)`) needs `Add n 1 nInc`; here n=restBranches,
  -- nInc=branches. PS doesn't commute `Add` automatically, so we
  -- supply both directions.
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
    -- BranchProver's mpv parameter is `mpvMax` (NOT `ruleMpv`) — every
    -- branch's CompiledProof presents the WRAP-LEVEL view of `mpv =
    -- mpvMax`. Mirrors OCaml `Pickles.compile_promise`'s output: all
    -- proofs share `'mlmb` (= wrap's max), with the per-branch actual
    -- width hidden inside `CompiledProof.widthData`'s GADT-existential.
    -- BranchProver is a newtype (not an alias) so PS sees a saturated
    -- type constructor in the instance head rather than an unfolded
    -- function type — dispatch resolves cleanly.
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
      -- Extract THIS branch's selfStepDomainLog2 from the FULL
      -- `Vector topBranches Int`. branchIdx is a runtime Int (cons
      -- depth k has branchIdx = k); the invariant `branchIdx <
      -- topBranches` is enforced by the Cons recursion's
      -- `Compare 0 topBranches LT` constraints.
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
          -- Pass the wrap circuit's `mpvMax`. `padShapeProveData`
          -- front-pads the per-rule proveData up to it with `Dummy.*`
          -- values; at `ruleMpv = mpvMax` that padding is empty.
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
--
-- Stored fields are intentionally NOT the rank-2 `StepRule` (PS rejects
-- rank-2 storage at the record-field level). Instead `mkRuleEntry`
-- packs monomorphic Effect-returning closures that capture the rule;
-- the closure bodies use the rule's rank-2 nature when invoked, where
-- PS handles it cleanly.
--------------------------------------------------------------------------------

-- | Per-rule entry packaged for storage in a multi-branch carrier.
-- | Stored fields are monomorphic closures over the rank-2 `StepRule`
-- | captured at `mkRuleEntry` time.
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
  { -- | Pre-pass: takes a placeholder `StepProveContext mpv` (built
    -- | with OCaml `rough_domains` log2=20) and returns the actual
    -- | `selfStepDomainLog2` derived by counting gates in a one-shot
    -- | constraint-system build. Analog of OCaml's
    -- | `Fix_domains.domains` per-rule.
    --
    -- | `nd` is the compilation-wide multi-domain count = the
    -- | proof-system's `branches` count, used for Pseudo dispatch
    -- | over Self-prev step domains in `finalizeOtherProofCircuit`.
    preComputeStepDomainLog2Fn ::
      AdviceHandler r -> PProveStep.StepProveContext mpv nd blueprints -> Effect Int
  , stepCompileFn ::
      AdviceHandler r -> PProveStep.StepProveContext mpv nd blueprints -> Effect PProveStep.StepCompileResult
  -- | `vkCarrier` is the spec-derived per-slot side-loaded VK carrier
  -- | (`SideloadedVKsCarrier prevsSpec vkCarrier`): compiled slots
  -- | contribute `Unit`, side-loaded slots contribute a runtime
  -- | `Pickles.Sideload.VerificationKey`. Threaded explicitly here
  -- | because PS rejects rank-2 polymorphic record fields — pinning
  -- | it as a `RuleEntry` parameter lets the closure body's
  -- | `stepSolveAndProve` see a saturated `StepAdvice`.
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

-- | Smart constructor: takes the user's rank-2 `StepRule` value and
-- | produces a `RuleEntry` with closures capturing it. Each closure's
-- | body invokes the captured rule against `stepCompile` /
-- | `stepSolveAndProve`.
mkRuleEntry
  :: forall @mpvMax @outputVal @prevInputVal @r
       prevsSpec mpv mpvPad nd ndPred outputSize valCarrier
       inputVal inputVar outputVar prevInputVar
       carrier carrierVar pad unfsTotal digestPlusUnfs
       compileSideloadedVkCarrier sideloadedVkCarrier blueprints
       vkSourcesCarrier
   . CircuitGateConstructor StepField VestaG
  -- `vkSourcesCarrier` is uniquely determined by `prevsSpec` (see the
  -- `prevsSpec -> vkCarrier` fundep on `BuildSlotVkSources`), so compile-
  -- and prove-path constraints share one binder. The two BuildSlotVkSources
  -- constraints differ only in their `cell` argument (compile-time VK
  -- descriptor vs prove-time `SideloadBundle.Bundle`).
  --
  -- Compile-path carrier: cells = side-loaded VK descriptor. Synthesised
  -- by `MkUnitVkCarrier` for the `getSideloadedVKsCarrier` Effect
  -- instance inside `stepCompile` / `preComputeStepDomainLog2`.
  -- A side-loaded tag's VK is a wrap VK, so it is `WrapVkChunks` like
  -- every other VK a step circuit reads. Distinct from the wrap
  -- circuit's `stepChunks`, which is the one count that varies.
  => BuildSlotVkSources (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean) prevsSpec WrapVkChunks mpv blueprints compileSideloadedVkCarrier vkSourcesCarrier
  => MkUnitVkCarrier prevsSpec compileSideloadedVkCarrier
  -- Prove-path carrier: cells = `SideloadBundle.SlotProveVk`, carrying
  -- a bundle exactly at the side-loaded slots. Sourced from
  -- `StepAdvice.sideloadedVKs` inside `stepSolveAndProve`.
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
  -- The rule already has the bare-`m` `StepRule` shape the step
  -- functions expect — pass it straight through (compile and prove use
  -- the same rule value).
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

-- Type synonym for `StepRuleAt`, used to avoid an import-cycle in the
-- `RuleEntry` field types. Pinned to the entry's monad `m` so an app
-- rule's advice constraints discharge at the concrete `m`.
type PStepRule r mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar =
  PProveStep.StepRuleAt r mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar

--------------------------------------------------------------------------------
-- compileMulti — N-branch compile entry point.
--
-- Type-variable layout:
--
--   * `rs` (kind `RulesSpec`) — per-rule HList of `(mpv, valCarrier,
--     prevsSpec, slotVKs)` quadruples.
--   * `rulesCarrier`, `proversCarrier`, `perBranchStepCarrier`,
--     `perBranchVKsCarrier` — Tuple chains shaped to match `rs`,
--     derived mechanically by `CompilableRulesSpec`'s instances.
--   * `inputVal` / `outputVal` / `prevInputVal` — SHARED across all
--     branches (the wrap VK's public-input layout is the same for any
--     proof under it).
--   * `mpvMax` — max over all rules' mpvs (caller-supplied).
--
-- Pipeline:
--
--   1. Walk `rs`: per-rule, run `stepCompile` independently. Each
--      branch's step circuit is sized by ITS OWN prevsSpec /
--      max_proofs_verified.
--   2. ONE wrap compile with `branches = N`, threading per-branch
--      `Vector branches` arrays into `WrapMainConfig.{stepWidths,
--      domainLog2s, stepKeys}`.
--   3. Per-branch prover wraps `runMultiProverBody` with that branch's
--      `whichBranch` field baked into the wrap statement.
--------------------------------------------------------------------------------

-- | Build a per-rule `StepProveContext` from the multi-branch config,
-- | the rule's `slotVKs`, and the per-branch step-domain log2 vector.
-- | Combines the shared `srs` / `debug` / `wrapDomainOverride` with
-- | the rule's own `slotVKs`, then feeds through
-- | `shapeCompileData @prevsSpec` for the per-prev-spec layout
-- | (per-slot lagrange basis, blinding H, FOP domains).
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
-- Pipeline:
--   1. mkStepAdvice @prevsSpec cfg stepCR wrapResult appInput prevs
--   2. shapeProveData @prevsSpec cfg wrapResult sideInfo prevs
--   3. stepProveFn ctx stepCR stepAdvice
--   4. compute step oracles + allEvals
--   5. wrapComputeDeferredValues
--   6. wrapSolveAndProve with `whichBranch: F (fromInt branchIdx)`
--   7. package CompiledProof
--
-- Top-level (not a class method) so per-rule type vars + constraints
-- stay localized to this function instead of leaking onto the class
-- instance head. `buildBranchProvers` calls this at each per-branch
-- closure, passing the captured `branchIdx` + per-branch step result.
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
  -- `topBranches` is the FIXED outer count threaded through
  -- `RuleEntry`'s `nd` and the multi-domain Vector consumed by
  -- `finalizeOtherProofCircuit`. Distinct from `branches` (the wrap
  -- circuit's per-branch lagrange + step-data carrier count): they
  -- currently coincide but stay separate type variables to match
  -- the rule-level signature shape.
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
  -- Step-half constraints reference the rule's own `mpv`. The wrap
  -- circuit operates at the (possibly wider) `mpvMax`/`slotsMax`
  -- shape; constraints below mirror that — they are independent of
  -- the rule's `mpv` / `slots`.
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
  -- ^ shared per-branch wrap config inputs (same vector used at
  --   wrap compile time via `buildWrapMainConfigMulti`); the wrap
  --   solver here rebuilds the same `WrapMainConfig` from this.
  -> Vector topBranches Int
  -- ^ FULL Vector of all branches' step domain log2s. Threaded
  --   to `buildStepProveCtx` so this rule's `finalizeOtherProofCircuit`
  --   has the multi-domain Pseudo dispatch table for Self-prev slots.
  --   Mirrors OCaml `compile.ml:568`'s `~step_domains:all_step_domains`.
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
    -- Pass the FULL `Vector topBranches Int` of all branches' step
    -- domain log2s. Drives multi-domain Pseudo dispatch in
    -- `finalizeOtherProofCircuit` for Self-prev slots — mirrors OCaml
    -- step_main's `step_domains:all_step_domains` (compile.ml:568).
    shape = shapeCompileData @prevsSpec perRuleCfg allStepDomainLog2s

  -- Per-prove side-loaded VK carrier from `stepInputs`. A rule with no
  -- side-loaded slot passes `NoSideLoadedVk` at every position; a slot
  -- keyed `SideLoadedKey` gets `SideLoadedVk` its runtime bundle,
  -- mirroring OCaml's `~handler`.
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

    -- Pad the rule's mpv-shaped proveData to the wrap circuit's mpvMax
    -- shape. Empty padding for single-rule callers (mpv = mpvMax);
    -- `padShapeProveData` front-pads with dummies for multi-rule
    -- callers where the rule's mpv < wrap's mpvMax.
    --
    -- Dummies sized at the wrap circuit's `mpvMax` mirror OCaml
    -- `step.ml:736-770`'s `extend_front ... Unfinalized.dummy` and
    -- the surrounding per-prev fields' analogous front-pad calls.
    outerMpvMax = reflectType (Proxy @mpvMax)
    -- EXPERIMENT: `Unfinalized.Constant.dummy` in OCaml is a SHARED
    -- singleton lazy, forced once globally; its alpha/beta/gamma/zeta
    -- consume Ro counters chal_1..4 (relative to the lazy's first
    -- force). PS's `baseCaseDummies` walks Ro in a SEQUENCE governed
    -- by `forceOrderFor`; for mpv=0 it's UnfinalizedFirst (= consume
    -- unfinalizedConstantDummy first → chal counters 1..4). Use mpv=0
    -- here so PS's chal_1..4 in `unfinalizedConstantDummy` line up
    -- with OCaml's lazy-force-from-clean-state semantics.
    bcdMax = baseCaseDummies { maxProofsVerified: 0 }
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

    -- `AllocEvals (F WrapField)` lifted from `bcd.dummyEvals`
    -- (`AllEvals WrapField`). Mirrors OCaml `dummy.ml:7-20`'s
    -- `Dummy.evals` — every field, including `publicEvals`, is
    -- populated by `Ro.tock ()` draws (NOT zero placeholders). The
    -- `Ro` stream is already advanced consistently with OCaml via
    -- `baseCaseDummies { maxProofsVerified: mpvMax }`.
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
      -- OCaml `wrap.ml:412-414` pads `wrap_domain_indices` with
      -- `Tock.Field.one` (NOT zero) when actualProofsVerified <
      -- maxProofsVerified. This matches the wrap circuit's
      -- expectation for `branch_data.domain` of a dummy slot
      -- (encodes `Pow_2_roots_of_unity 14` = the wrap circuit's own
      -- domain, all_possible_domains[1]).
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
        -- FFI-shaped `prevChallenges` for the step proof's oracles.
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

        -- Chunked step-proof evaluations: one `PointEval` per polynomial
        -- per chunk. Wrap prover consumes this directly via the chunked
        -- CIP / chunked sponge replay.
        stepProofData = pallasProofData @StepIPARounds stepResult.proof
        chunkedEvals =
          { ftEval1: stepOracles.ftEval1
          -- Public eval from the proof's own `evals.public`. The kimchi prover
          -- always populates it (`prover.rs:996`, chunked via
          -- `to_chunked_polynomial num_chunks`), and the chunked verifier
          -- *requires* `Some` (`verifier.rs:334` errors otherwise). This carries
          -- the full `nc` chunks (= OCaml `wrap.ml:111` `proof.public_evals`).
          -- The oracle binding (`oracles.rs:113`) collapses to chunk-0 only, so
          -- using `stepOracles.publicEvals` silently dropped the higher chunks
          -- and broke the chunked CIP fold (`ft_eval0.pEval0Folded`).
          , publicEvals: stepProofData.evals.public
          , zEvals: stepProofData.evals.z
          , witnessEvals: stepProofData.evals.w
          , coeffEvals: stepProofData.evals.coefficients
          , sigmaEvals: stepProofData.evals.s
          , indexEvals: stepProofData.evals.indexEvals
          }

        -- Collapsed (Horner-combined) view of `chunkedEvals`, kept on
        -- the `CompiledProof` as a transitional shim for recursive-step
        -- consumers that still take a single-eval `AllEvals`
        -- (`Pickles.Prove.Step`'s `wrapPrevEvals` / `stepAdvicePrevEvals`).
        -- At step num_chunks=1 this is byte-identical to the only chunk;
        -- at num_chunks>1 it is the correct Horner combine. The chunked
        -- refactor of those consumers is the next phase of task #63.
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

        -- Step PI is `mpvMax`-shaped (the unfinalized-proofs vector is
        -- front-padded from the rule's `len` up to `mpvMax`), so the
        -- outer-hash digest sits at offset `mpvMax * 32`, NOT the rule's
        -- own `mpv * 32`. The index is bounded by `outputSize = mpvMax *
        -- 32 + 1 + mpvMax` from the constraint chain in scope (`Mul mpvMax
        -- 32 unfsTotal`, `Add unfsTotal 1 digestPlusUnfs`, `Add
        -- digestPlusUnfs mpvMax outputSize`); enforced at runtime via
        -- `unsafeFinite`.
        msgStep =
          let
            F f = Vector.index stepResult.publicOutputs
              (unsafeFinite @outputSize (outerMpvMax * 32))
          in
            f

        stepProofSg = (pallasProofData @StepIPARounds stepResult.proof).opening.sg

        dummyWrapExpanded = dummyIpaChallenges.wrapExpanded

        -- Use the wrap circuit's `mpvMax`-derived bcd (same one feeding
        -- `padDummies` above) so the front-pad dummies and the
        -- `padShapeProveData` dummies share an Ro stream. Required when
        -- `mpv < mpvMax`: otherwise the wrap circuit's permutation
        -- argument doesn't close.
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

        -- Wrap statement + advice (with whichBranch baked per-branch via
        -- `F (fromInt branchIdx)`) and the wrap solver context.
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
            -- Recover the rule's user-defined `publicOutput` from
            -- stepResult.userPublicOutputFields (populated post-solve via
            -- the stepMain Ref). NOT stepResult.publicOutputs (which is
            -- the kimchi public-output vector = digest+unfinalized+
            -- wrap-msgs).
            publicOutput =
              fieldsToValue @StepField stepResult.userPublicOutputFields

          let
            widthData = mkSomeCompiledProofWidthData @mpv @pad
              { oldBulletproofChallenges: proveData.prevStepChallenges
              , msgWrapChallenges: proveData.msgWrapChallenges
              , outerStepChalPolyComms:
                  map (\e -> AffinePoint { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
              -- Front-padding dummies for the `Vector PaddedLength` views
              -- mkSomeCompiledProofWidthData precomputes. Match what
              -- mkStepAdvice / shapeProveData's InductivePrev case fills the
              -- pad slots with: `dummyIpaChallenges.stepExpanded` for
              -- the inner step proof's prev bp-chals, the wrap-side dummy
              -- challenge for the outer wrap-IPA bp-chals, and
              -- `dummyWrapSgInStepField` for the outer step proof's IPA sg.
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
            -- Full `nc`-chunk public eval from the proof (see `chunkedEvals`
            -- note above); recursive consumers read this via `prevData.proof.pEval0Chunks`.
            , pEval0Chunks: map _.zeta (NonEmptyArray.toArray stepProofData.evals.public)
            , challengePolynomialCommitment: stepProofSg
            -- The statement's fields, input then output: what the step
            -- circuit hashed into the step message digest (`hashAppFields`).
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
  -- Strict-equality enforcement: `mpvMax = max(ruleMpv across rs)`,
  -- not just `≥` (which the per-rule `Add mpvPad _ mpvMax` constraints inside
  -- `CompilableRulesSpecShape` already provide). Mirrors OCaml's
  -- `compile_promise ~max_proofs_verified:(module Nat.NX)` where X is
  -- the actual max across rules' prev counts.
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
  -- Step 1: per-rule pre-pass + step compile.
  --
  -- `runMultiCompileFull` calls `prePassDomainLog2s` then
  -- `runMultiCompile` with the FULL `Vector branches Int` of all
  -- branches' step domain log2s, delivering OCaml `compile.ml:568`'s
  -- `~step_domains:all_step_domains` pattern: every branch's step
  -- circuit sees the full multi-domain vector for Self-prev Pseudo
  -- dispatch.
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

  -- Validate declared @stepChunks against per-branch num_chunks
  -- computed from the actual step domain sizes. kimchi formula
  -- (constraints.rs:974-978): `if domain_size < max_poly_size then 1
  -- else domain_size / max_poly_size`. With log2s: at step_log2 <=
  -- StepIPARounds (= 16, i.e. 2^16 = max_poly_size), the branch needs
  -- 1 chunk; otherwise `2^(log2 - 16)` chunks. Every branch must agree
  -- with the user's declaration.
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
  --
  -- Port of OCaml `compile.ml:850-864`, including its wording.
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

  -- Step 3: build per-branch BranchProver closures (each captures its
  -- branchIdx for `whichBranch` baking in the wrap statement). The
  -- FULL `Vector branches Int` of step-domain log2s is shared by
  -- every branch's `runMultiProverBody` for `buildStepProveCtx`'s
  -- multi-domain dispatch table.
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
    -- Wrap circuit's own domain log2 (= wrap_domains[mpvMax]).
    -- Used by the verifier for wrap-side proof validation; not
    -- consumed by the wrap circuit body anymore (the wrap circuit
    -- now picks per-branch lagrange bases from `perBranchLagrangeAt`,
    -- mirroring OCaml `lagrange_with_correction`).
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
