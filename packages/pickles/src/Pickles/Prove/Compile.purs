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
-- | Everything that differs between `Unit` / `Slot Compiled`
-- | shapes lives inside `CompilableSpec`'s instances; `compile`
-- | dispatches through them.
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
  , class PadProveDataMpv
  , padShapeProveData
  , class ConvertSlots
  , convertSlots
  , class CompilableRulesSpec
  , branchCount
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

import Control.Monad.Except (ExceptT)
import Data.Enum (fromEnum)
import Data.Exists (runExists)
import Data.Fin (unsafeFinite)
import Data.Functor.Product (Product, product)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over, wrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.Constants (roughDomainsLog2, zkRows)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
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
import Pickles.ProofFFI
  ( pallasProverIndexDomainLog2
  , permutationVanishingPolynomial
  , proofCoefficientEvals
  , proofIndexEvals
  , proofSigmaEvals
  , proofWitnessEvals
  , proofZEvals
  , vestaProofOracles
  , vestaSrsBlindingGenerator
  , vestaSrsLagrangeCommitmentAt
  ) as ProofFFI
import Pickles.ProofsVerified (ProofsVerifiedCount, boolVecToProofsVerified)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap
  ( WrapDeferredValuesInput
  , assembleWrapMainInput
  , wrapComputeDeferredValues
  )
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
import Pickles.Sideload.Advice (class MkUnitVkCarrier, class SideloadedVKsCarrier)
import Pickles.Sideload.Bundle (Bundle, projectVk, verifierIndex) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey(..)) as SLVK
import Pickles.Slots (Compiled, SideLoaded, Slot)
import Pickles.Step.Dummy
  ( baseCaseDummies
  , computeDummySgValues
  , wrapDomainLog2ForProofsVerified
  , wrapDummyUnfinalizedProof
  )
import Pickles.Step.Dummy as Dummy
import Pickles.Step.Main (class BuildSlotVkSources, SlotVkBlueprintCompiled(..), SlotVkBlueprintSideLoaded)
import Pickles.Step.Main as MpvPadding
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier)
import Pickles.Step.Types as Step
import Pickles.Types
  ( MaxProofsVerified
  , PaddedLength
  , PerProofUnfinalized(..)
  , PointEval(..)
  , StatementIO(..)
  , StepAllEvals(..)
  , StepIPARounds
  , WrapIPARounds
  )
import Pickles.Util.Unique (Unique, newUnique)
import Pickles.Verify
  ( CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , Verifier
  , mkSomeCompiledProofWidthData
  , mkVerifier
  , verify
  , verifyOne
  , wrapPublicInput
  )
import Pickles.Verify.Types (toPlonkMinimal)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (class PadSlots, NoSlots, noSlots, replicateSlots)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (EQ, GT, LT)
import Prim.Ordering as PrimOrdering
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, UnChecked(..), coerceViaBits)
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
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
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
-- | The phantom `(inputVal, outputVal, mpv)` parameters provide
-- | structural type safety — different-shape rules' tags can't be
-- | substituted for each other. Same-shape collisions surface at
-- | runtime (mismatched `unique` → wrong VK in proof).
-- |
-- | Mirrors OCaml's `Tag.t` (`pickles/tag.mli`): the `unique` is the
-- | analog of `Type_equal.Id.uid`, the phantom params analog of the
-- | OCaml type parameters.
newtype Tag :: Type -> Type -> Int -> Type
newtype Tag inputVal outputVal mpv = Tag
  { unique :: Unique
  , verifier :: Verifier
  }

derive instance Newtype (Tag inputVal outputVal mpv) _

-- | VK bundle downstream compiles consume as `perSlotImportedVKs`.
type ProverVKs =
  { stepCompileResult :: StepCompileResult
  , wrapCompileResult :: WrapCompileResult
  , wrapDomainLog2 :: Int
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
data SlotWrapKey
  = Self
  | External ProverVKs

type StepInputs :: Type -> Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier vkCarrier =
  { appInput :: inputVal
  , prevs :: prevsCarrier
  -- | Spec-indexed runtime side-loaded VK carrier. Compiled-only
  -- | specs (NRR/Simple_chain/Tree/TwoPhaseChain) populate this with
  -- | `mkUnitVkCarrier @prevsSpec` (an all-Unit chain — semantically
  -- | identical to omitting the field). Specs containing
  -- | `Slot SideLoaded` slots populate the corresponding
  -- | slot positions with real `Pickles.Sideload.VerificationKey`
  -- | bundles. Mirrors OCaml's per-prove `~handler`: the runtime VK
  -- | is bound at prove time, not at compile time.
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
data PrevSlot :: Type -> Int -> Type -> Type -> Type
data PrevSlot inputVal n stmt outputVal
  = BasePrev { dummyStatement :: stmt }
  | InductivePrev
      (CompiledProof n stmt outputVal Unit)
      (Tag inputVal outputVal n)

type CompileConfig :: Type -> Type -> Type
type CompileConfig prevsSpec slotVKs =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , perSlotImportedVKs :: slotVKs
  , debug :: Boolean
  -- | OCaml `override_wrap_domain` (`compile.ml`). When `Just o`, the
  -- | rule's wrap circuit uses domain log2 `o` instead of the default
  -- | `wrap_domains.h` (`common.ml:25-29`: N0→13, N1→14, N2→15).
  -- | Affects the per-slot lagrange basis for self-recursive slots and
  -- | the wrap circuit's own kimchi domain. Tree_proof_return uses
  -- | `Just 14` (override:N1) per OCaml `dump_tree_proof_return.ml`.
  , wrapDomainOverride :: Maybe Int
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
-- | * `slotsValue` — runtime realisation of the `slots` type
-- |   constructor (`noSlots`, `slots1 ...`, etc.) carrying each prev's
-- |   wrap bp-challenges.
type ShapeCompileData :: Int -> Int -> Type -> (Type -> Type) -> Type
type ShapeCompileData mpv nd blueprints slots =
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
-- |   `dummyWrapTockPublicInput` arrays, passed to `vestaProofOracles`
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
-- | Fields are Vector mpv (one entry per slot); runProverBody pads the
-- | mpv-sized vectors to wrap-hack Vector 2 where needed and computes
-- | the proofs-verified mask from `mpv` directly.
-- |
-- | Nil provides empty vectors (Vector.nil for everything, noSlots for
-- | `slotsValue`). Cons recursively cons each slot's entry onto the
-- | tail from `shapeProveData @rest`.
type ShapeProveData :: Int -> (Type -> Type) -> Type
type ShapeProveData mpv slots =
  { prevSgs :: Vector mpv (AffinePoint WrapField)
  , prevStepChallenges :: Vector mpv (Vector StepIPARounds StepField)
  , msgWrapChallenges :: Vector mpv (Vector WrapIPARounds WrapField)
  , prevUnfinalizedProofs ::
      Vector mpv
        (PerProofUnfinalized WrapIPARounds (Type2 (F WrapField)) (F WrapField) Boolean)
  , prevStepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  , prevEvals :: Vector mpv (StepAllEvals (F WrapField))
  , prevWrapDomainIndices :: Vector mpv (F WrapField)
  , kimchiPrevEntries ::
      Vector mpv
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  -- | Runtime realisation of the `slots` type constructor carrying
  -- | each prev's wrap bp-challenges.
  , slotsValue :: slots (Vector WrapIPARounds (F WrapField))
  }

--------------------------------------------------------------------------------
-- PadProveDataMpv — convert ShapeProveData mpv slots → ShapeProveData
-- mpvMax slotsMax. Mirrors the rule's actual mpv/slots shape (driven by
-- prevsSpec) up to the wrap circuit's wider mpvMax/slotsMax.
--
-- The two-instance chain uses `else instance` (PS overlapping-instance
-- syntax). PS picks the first matching instance, so the identity head
-- with repeated vars (`mpv slots mpv slots`) fires whenever the types
-- align (single-rule callers, where `mpv = mpvMax` and `slots =
-- slotsMax`); otherwise the general instance front-pads each Vector
-- field via `PadProveDataDummies` and converts the slots carrier via
-- `ConvertSlots`.
--------------------------------------------------------------------------------

-- | Per-entry dummy values for padding. Each field is one entry's
-- | worth — the general `PadProveDataMpv` instance front-pads each
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
  , dummyPrevEvals :: StepAllEvals (F WrapField)
  , dummyPrevWrapDomainIdx :: F WrapField
  , dummyKimchiPrevEntry ::
      { sgX :: StepField
      , sgY :: StepField
      , challenges :: Vector WrapIPARounds WrapField
      }
  , dummySlotChal :: Vector WrapIPARounds (F WrapField)
  }

-- | Convert one slots-carrier shape to another, filling any new slots
-- | with the supplied dummy. Two instances:
-- |
-- |   * Identity (`slotsSrc = slotsDst`) — pass through.
-- |   * Fallback for `slotsSrc = NoSlots`: produce a fresh `slotsDst a`
-- |     populated by `replicateSlots` from `Pickles.Wrap.Slots`.
-- |
-- | The `NoSlots → slotsDst` case is what TwoPhaseChain b0 needs (rule
-- | has 0 prev proofs, wrap circuit has 1 slot of width 1). Other
-- | conversions (e.g. `Slots1 1 → Slots2 1 2`) are not yet implemented
-- | — adding them needs structural induction on `slotsDst`'s widths.
class ConvertSlots (slotsSrc :: Type -> Type) (slotsDst :: Type -> Type) where
  convertSlots :: forall a. a -> slotsSrc a -> slotsDst a

instance ConvertSlots slotsSrc slotsSrc where
  convertSlots _ = identity

else instance
  ( PadSlots slotsDst mpvDst
  , Reflectable mpvDst Int
  ) =>
  ConvertSlots NoSlots slotsDst where
  convertSlots dummy _ = replicateSlots dummy

-- | Pad a `ShapeProveData mpv slots` to `ShapeProveData mpvMax slotsMax`.
-- |
-- | When `mpv = mpvMax` and `slots = slotsMax`, the conversion is the
-- | identity (the fast-path instance below). Otherwise the rule's mpv
-- | is strictly less than the wrap circuit's mpvMax; the prov-data
-- | needs front-padding with `Dummy.*` values to match the wrap
-- | circuit's expected shape (the general instance below).
class PadProveDataMpv (mpv :: Int) (slots :: Type -> Type) (mpvMax :: Int) (slotsMax :: Type -> Type) where
  padShapeProveData
    :: PadProveDataDummies
    -> ShapeProveData mpv slots
    -> ShapeProveData mpvMax slotsMax

-- | Fast-path: rule's mpv/slots equal the wrap circuit's mpvMax/slotsMax.
-- | Identity. Single-rule callers all hit this — preserves byte-identical
-- | witness (the cast is a tautology since both sides are the same type).
instance PadProveDataMpv mpv slots mpv slots where
  padShapeProveData _ = identity

-- | General fallback: rule's mpv < wrap's mpvMax. Front-pads each
-- | `Vector mpv` field with `mpvPad = mpvMax - mpv` copies of the
-- | corresponding dummy, and converts the slots carrier via
-- | `ConvertSlots`. Mirrors OCaml `step.ml:736-770`'s `extend_front
-- | unfinalized_proofs ... Unfinalized.dummy` and analog padding for
-- | the other per-prev fields.
else instance
  ( ConvertSlots slots slotsMax
  , Add mpvPad mpv mpvMax
  , Reflectable mpvPad Int
  ) =>
  PadProveDataMpv mpv slots mpvMax slotsMax where
  padShapeProveData dummies sd =
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
    , slotsValue: convertSlots dummies.dummySlotChal sd.slotsValue
    }

--------------------------------------------------------------------------------
-- CompilableSpec — the shape-dependent dispatch class
--------------------------------------------------------------------------------

-- | Shape-specific data provider. Instances provide small per-shape
-- | method bodies; the full compile flow (`runCompile`, below) is
-- | a single top-level polymorphic function that dispatches through
-- | these methods.
-- |
-- | Fundeps `prevsSpec -> slotVKs prevsCarrier mpv slots` mean the
-- | user only pins `prevsSpec`; the other four axes are derived.
class CompilableSpec
  :: Type
  -> Type
  -> Type
  -> Int
  -> (Type -> Type)
  -> Type
  -> Type
  -> Type
  -> Type
  -> Constraint
class
  CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier vkCarrier blueprints
  | prevsSpec -> slotVKs prevsCarrier mpv slots valCarrier carrier vkCarrier blueprints
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
    => CompileConfig prevsSpec slotVKs
    -> Vector nd Int
    -> ShapeCompileData mpv nd blueprints slots

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
    => CompileConfig prevsSpec slotVKs
    -> StepCompileResult
    -> WrapCompileResult
    -> inputVal
    -> prevsCarrier
    -> vkCarrier
    -> Effect
         { stepAdvice ::
             StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal mpv
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
    :: CompileConfig prevsSpec slotVKs
    -> WrapCompileResult
    -> ShapeProveSideInfo mpv
    -> prevsCarrier
    -> vkCarrier
    -> ShapeProveData mpv slots

--------------------------------------------------------------------------------
-- CompilableSpec Unit (N=0, NRR-shape)
--------------------------------------------------------------------------------

instance CompilableSpec Unit Unit Unit 0 NoSlots Unit Unit Unit Unit where
  shapeCompileData cfg _ =
    { stepProveCtx:
        { srsData:
            { perSlotLagrangeAt: Vector.nil
            , blindingH:
                coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs
            , perSlotFopDomainLog2s: Vector.nil
            , perSlotVkBlueprints: unit
            }
        , dummySg: nrrDummyWrapSg cfg.srs.pallasSrs cfg.srs.vestaSrs
        , crs: cfg.srs.vestaSrs
        , debug: cfg.debug
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
      -- Nil has no prev slots, so `stepDomainLog2` is dead — the
      -- per-slot dummy that consumes it gets replicated to a
      -- `Vector 0` (= empty). `0` is a sentinel; any value works.
      StepAdvice base = buildStepAdvice @Unit
        { publicInput: appInput
        , stepDomainLog2: 0
        , prevAppStates: unit
        , sideloadedVKs: unit
        }
      bcd = Dummy.baseCaseDummies { maxProofsVerified: 0 }
      dummyHash = mkDummyMsgWrapHash bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      stepAdvice = StepAdvice
        ( base
            { wrapVerifierIndex = extractWrapVKCommsAdvice wrapCR.verifierIndex
            , messagesForNextWrapProofDummyHash = dummyHash
            }
        )
    in
      pure
        { stepAdvice
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
    , slotsValue: noSlots
    }

--------------------------------------------------------------------------------
-- CompilableSpec Slot Compiled (N ≥ 1, recursive)
--------------------------------------------------------------------------------

-- | Recursive instance covering all `Slot Compiled n stmt /\ rest` shapes.
-- | Derives `mpv`, `prevsCarrier`, and `slots` by recursing through `rest`.
instance
  ( CompilableSpec rest restSlotVKs restPrevsCarrier restMpv restSlots restValCarrier restCarrier restVkCarrier restScaffolds
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
    (Slot Compiled n (StatementIO prevHeadInput prevHeadOutput) /\ rest)
    (SlotWrapKey /\ restSlotVKs)
    ( PrevSlot prevHeadInput n (StatementIO prevHeadInput prevHeadOutput) prevHeadOutput
        /\ restPrevsCarrier
    )
    mpv
    (Product (Vector n) restSlots)
    (StatementIO prevHeadInput prevHeadOutput /\ restValCarrier)
    ( Step.PerProofWitness
        n
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
        /\ restCarrier
    )
    -- Compiled slots ignore the runtime side-loaded VK; the head
    -- entry of the carrier is `Unit`. Mirrors
    -- `Pickles.Sideload.Advice.SideloadedVKsCarrier`'s
    -- `Slot Compiled → Unit /\ restCarrier` instance.
    (Unit /\ restVkCarrier)
    -- Compile-time blueprint for this slot's wrap-VK source. `Self`
    -- becomes `VkBlueprintShared`; `External` becomes `VkBlueprintConst`.
    -- Bundled into the post-walk `SlotVkSource` by
    -- `buildSlotVkSources` at circuit-build time.
    (SlotVkBlueprintCompiled /\ restScaffolds)
  where
  shapeCompileData cfg selfStepDomainLog2s =
    let
      headSlotWrapKey /\ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      restShape = shapeCompileData @rest restCfg selfStepDomainLog2s
      outerMpv = reflectType (Proxy @mpv)
      outerWrapDomainLog2 = case cfg.wrapDomainOverride of
        Just o -> o
        Nothing -> Dummy.wrapDomainLog2ForProofsVerified outerMpv

      -- Slot's wrap domain (drives lagrange basis for slot's IVP).
      -- Self → outer rule's wrap_domain (with override applied);
      -- External → imported rule's wrap_domain.
      slotWrapDomainLog2 = case headSlotWrapKey of
        External vks -> vks.wrapDomainLog2
        Self -> outerWrapDomainLog2

      -- Slot's source proof system's unique step-domain log2s
      -- (mirrors OCaml `domain_for_compiled`'s `domains` argument):
      --   * Self → outer rule's compilation-wide unique_domains
      --     (passed in as `selfStepDomainLog2s`, full Vector nd).
      --   * External → imported rule's domains. Currently we only
      --     support External → single-rule sources, so we replicate
      --     the imported rule's single step domain log2 across nd
      --     slots. For our test set (TreeProofReturn NRR external
      --     with nd=1) this gives the correct `Vector 1 [importedLog2]`.
      slotFopDomainLog2s = case headSlotWrapKey of
        Self -> selfStepDomainLog2s
        External vks ->
          Vector.replicate
            (ProofFFI.pallasProverIndexDomainLog2 vks.stepCompileResult.proverIndex)

      slotLagrange =
        mkConstLagrangeBaseLookup \i ->
          coerce (ProofFFI.vestaSrsLagrangeCommitmentAt cfg.srs.pallasSrs slotWrapDomainLog2 i)

      outerBcd = Dummy.baseCaseDummies { maxProofsVerified: outerMpv }
      outerDummySgs = Dummy.computeDummySgValues outerBcd cfg.srs.pallasSrs cfg.srs.vestaSrs

      -- Reference: OCaml `step_main.ml:514-528`.
      headSlotScaffold = case headSlotWrapKey of
        Self -> VkBlueprintShared
        External vks ->
          VkBlueprintConst (extractWrapVKCommsAdvice vks.wrapCompileResult.verifierIndex)
    in
      { stepProveCtx:
          { srsData:
              { perSlotLagrangeAt:
                  slotLagrange :< restShape.stepProveCtx.srsData.perSlotLagrangeAt
              , blindingH:
                  coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs
              , perSlotFopDomainLog2s:
                  slotFopDomainLog2s
                    :< restShape.stepProveCtx.srsData.perSlotFopDomainLog2s
              , perSlotVkBlueprints:
                  headSlotScaffold /\ restShape.stepProveCtx.srsData.perSlotVkBlueprints
              }
          , dummySg: outerDummySgs.ipa.wrap.sg
          , crs: cfg.srs.vestaSrs
          , debug: cfg.debug
          }
      , wrapDomainLog2: outerWrapDomainLog2
      }

  mkStepAdvice cfg stepCR wrapCR appInput (headSlot /\ restPrevs) (_ /\ restVkCarrier) = do
    let
      slotN = reflectType (Proxy @n)
      headSlotWrapKey /\ _ = cfg.perSlotImportedVKs

      -- Self/External dispatch (OCaml `step.ml:751-754`). `Self` honours
      -- `cfg.wrapDomainOverride` (= OCaml `override_wrap_domain`);
      -- `External`'s wrapDomainLog2 already encodes its own override.
      outerOverridenWrapDomainLog2 = case cfg.wrapDomainOverride of
        Just o -> o
        Nothing -> Dummy.wrapDomainLog2ForProofsVerified slotN
      slotParams =
        case headSlotWrapKey of
          Self ->
            { slotWrapVK: wrapCR.verifierIndex
            , slotWrapDomainLog2: outerOverridenWrapDomainLog2
            , slotStepDomainLog2:
                ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex
            }
          External vks ->
            { slotWrapVK: vks.wrapCompileResult.verifierIndex
            , slotWrapDomainLog2: vks.wrapDomainLog2
            , slotStepDomainLog2:
                ProofFFI.pallasProverIndexDomainLog2 vks.stepCompileResult.proverIndex
            }

      -- Slot-specific dummies sized by this slot's prev rule's mpv (= n),
      -- not the outer rule's mpv.
      bcd = Dummy.baseCaseDummies { maxProofsVerified: slotN }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      dummyWrapSg = dummySgs.ipa.wrap.sg
      dummyStepSg = dummySgs.ipa.step.sg

      proofsVerifiedMask :: Vector MaxProofsVerified Boolean
      proofsVerifiedMask = (slotN >= 2) :< (slotN >= 1) :< Vector.nil

      stepEndoScalarF :: StepField
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

            fopProofState = Dummy.stepDummyUnfinalizedProof @n bcd
              { domainLog2: Dummy.wrapDomainLog2ForProofsVerified slotN }
              (map SizedF.wrapF bcd.ipaStepChallenges)

            baseCaseWrapPI = dummyWrapTockPublicInput @n
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
                -- branch_data.domain_log2 of the prev's wrap statement
                -- holds the prev's step domain (per OCaml
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
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            prevStepBpChalsExpanded :: Vector StepIPARounds StepField
            prevStepBpChalsExpanded =
              map
                ( \sc ->
                    toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                      stepEndoScalarF
                )
                prev.rawBulletproofChallenges

            wrapPI :: Array WrapField
            wrapPI = wrapPublicInput prevVerifier prevCp
          in
            runExists
              ( \(CompiledProofWidthData wd) ->
                  let
                    prevZetaField :: StepField
                    prevZetaField =
                      coerce
                        (toFieldPure prev.rawPlonk.zeta (F prevVerifier.stepEndo))

                    -- The prev's branch-specific step domain. The shared
                    -- `prevVerifier.stepDomainLog2` is a placeholder (first
                    -- branch's); use the proof's own `stepDomainLog2` so
                    -- multi-branch dispatch picks the right domain for each
                    -- prev. Mirrors OCaml `branch_data.domain_log2` driving
                    -- `step_domain` inside `expand_deferred`.
                    prevStepGenerator :: StepField
                    prevStepGenerator = domainGenerator prev.stepDomainLog2

                    prevStepShifts :: Vector 7 StepField
                    prevStepShifts = domainShifts prev.stepDomainLog2

                    prevVanishesOnZk :: StepField
                    prevVanishesOnZk = ProofFFI.permutationVanishingPolynomial
                      { domainLog2: prev.stepDomainLog2
                      , zkRows: prevVerifier.stepZkRows
                      , pt: prevZetaField
                      }

                    prevDv = expandDeferredForVerify
                      { rawPlonk: prev.rawPlonk
                      , rawBulletproofChallenges: prev.rawBulletproofChallenges
                      , branchData: prev.branchData
                      , spongeDigestBeforeEvaluations:
                          prev.spongeDigestBeforeEvaluations
                      , allEvals: prev.prevEvals
                      , pEval0Chunks: prev.pEval0Chunks
                      , oldBulletproofChallenges: wd.oldBulletproofChallenges
                      , domainLog2: prev.stepDomainLog2
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
                      wd.outerStepChalPolyCommsPadded
                      wd.msgWrapChallengesPadded

                    prevPaddedWrapBpChals
                      :: Vector PaddedLength (Vector WrapIPARounds WrapField)
                    prevPaddedWrapBpChals = wd.msgWrapChallengesPadded

                    prevPaddedStepHashChals
                      :: Vector PaddedLength (Vector StepIPARounds StepField)
                    prevPaddedStepHashChals = wd.oldBulletproofChallengesPadded

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
                    { prevStatement: prev.statement
                    , stepOpeningSg: prev.challengePolynomialCommitment
                    , kimchiPrevSg: prev.challengePolynomialCommitment
                    , wrapProof: prev.wrapProof
                    , wrapPublicInputArr: wrapPI
                    , prevChalPolys: prevPaddedChalPolys
                    , wrapPlonkRaw:
                        { alpha: SizedF.unwrapF prevDv.plonk.alpha
                        , beta: SizedF.unwrapF prevDv.plonk.beta
                        , gamma: SizedF.unwrapF prevDv.plonk.gamma
                        , zeta: SizedF.unwrapF prevDv.plonk.zeta
                        }
                    , wrapPrevEvals: prev.prevEvals
                    , wrapBranchData: prev.branchData
                    , wrapSpongeDigest: prev.spongeDigestBeforeEvaluations
                    , mustVerify: true
                    , wrapOwnPaddedBpChals: prevPaddedWrapBpChals
                    , fopState
                    , stepAdvicePrevEvals: prev.prevEvals
                    , kimchiPrevChallengesExpanded: prevStepBpChalsExpanded
                    , prevChallengesForStepHash: prevPaddedStepHashChals
                    }
              )
              prev.widthData
    -- Per-slot helper: build THIS slot's contribution (PS analog of
    -- OCaml `expand_proof` at `step.ml:122-150`). Mirrors OCaml's
    -- `expand_proof dlog_vk dlog_index app_state p data ~must_verify`
    -- per-slot call inside the `go` recursion (`step.ml:736-770`).
    contrib <- buildSlotAdvice @n
      { publicInput: appInput
      , prevStatement: slotData.prevStatement
      , wrapDomainLog2: slotParams.slotWrapDomainLog2
      , stepDomainLog2: slotParams.slotStepDomainLog2
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

    -- Recurse on `rest`, then cons head's slot pieces onto rest's
    -- per-slot vectors. Mirrors OCaml `step.ml:756-769` consing each
    -- per-slot output onto the rest's vectors. Carrier and valCarrier
    -- assemble heterogeneously: `slotSppw /\ restCarrier`,
    -- `stmt /\ restValCarrier`.
    let
      _ /\ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
    restResult <- mkStepAdvice @rest restCfg stepCR wrapCR appInput restPrevs restVkCarrier

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
        , wrapVerifierIndex: extractWrapVKCommsAdvice wrapCR.verifierIndex
        , kimchiPrevChallenges:
            contrib.slotKimchiPrevEntry :< restA.kimchiPrevChallenges
        , prevAppStates: slotData.prevStatement /\ restA.prevAppStates
        -- Compiled slot contributes Unit; mirrors
        -- `SideloadedVKsCarrier`'s `Slot Compiled` instance shape.
        , sideloadedVKs: unit /\ restA.sideloadedVKs
        }
    pure
      { stepAdvice: combinedAdvice
      , challengePolynomialCommitments:
          contrib.challengePolynomialCommitment :< restResult.challengePolynomialCommitments
      , baseCaseWrapPublicInputs:
          slotData.wrapPublicInputArr :< restResult.baseCaseWrapPublicInputs
      }

  shapeProveData cfg wrapCR sideInfo (headSlot /\ restPrevs) (_ /\ restVkCarrier) =
    let
      headSlotWrapKey /\ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      slotN = reflectType (Proxy @n)

      -- Per-slot params (matches `mkStepAdvice`'s SlotWrapKey dispatch):
      -- Self → outer rule's wrap VK; External → imported rule's wrap VK.
      slotWrapVK =
        case headSlotWrapKey of
          Self -> wrapCR.verifierIndex
          External vks -> vks.wrapCompileResult.verifierIndex

      -- Slot's wrap domain log2: Self honours the outer rule's
      -- `wrapDomainOverride`; External slots use the imported rule's
      -- stored wrapDomainLog2. Same logic as `shapeCompileData`'s
      -- slotParams.
      outerOverridenWrapDomainLog2 = case cfg.wrapDomainOverride of
        Just o -> o
        Nothing -> Dummy.wrapDomainLog2ForProofsVerified slotN

      slotWrapDomainLog2 :: Int
      slotWrapDomainLog2 = case headSlotWrapKey of
        External vks -> vks.wrapDomainLog2
        _ -> outerOverridenWrapDomainLog2

      -- Slot-specific dummies sized by the slot's prev rule's mpv (= n),
      -- not the outer rule's mpv. Matters for Tree-style heterogeneous
      -- slots: slot 0 (NRR, n=0) uses N=0-shaped dummies, slot 1 (Self,
      -- n=2) uses N=2-shaped dummies.
      bcd = Dummy.baseCaseDummies { maxProofsVerified: slotN }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      wrapSgD = dummySgs.ipa.wrap.sg -- AffinePoint StepField
      stepSgD = dummySgs.ipa.step.sg -- AffinePoint WrapField

      { head: PerProofUnfinalized headUnfRaw, tail: tailUnfinalized } =
        Vector.uncons sideInfo.unfinalizedSlots
      { head: headChalPolyComm, tail: tailChalPolyComms } =
        Vector.uncons sideInfo.challengePolynomialCommitments
      { head: headBaseCaseWrapPI, tail: tailBaseCaseWrapPIs } =
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

      -- msgForNextWrap real challenges, computed by endo-expanding the
      -- head slot's raw bp challenges via the wrap endo scalar.
      wrapEndoScalar :: WrapField
      wrapEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

      msgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      msgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField) wrapEndoScalar
          )
          headUnfRaw.bulletproofChallenges

      stepEndoScalarF :: StepField
      stepEndoScalarF =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

      slotData = case headSlot of
        BasePrev _ ->
          let
            baseCaseDummyChalPoly =
              { sg: wrapSgD, challenges: dummyIpaChallenges.wrapExpanded }
            toFFI r =
              { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
            dummyWrapOracles =
              ProofFFI.vestaProofOracles slotWrapVK
                { proof: dummyWrapProof bcd
                , publicInput: headBaseCaseWrapPI
                , prevChallenges: map toFFI [ baseCaseDummyChalPoly, baseCaseDummyChalPoly ]
                }
            dummyWrapXhatZeta = dummyWrapOracles.publicEvalZeta
            dummyWrapXhatOmegaZeta = dummyWrapOracles.publicEvalZetaOmega
            de = bcd.dummyEvals
            pe = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
            headPrevEvals = StepAllEvals
              { ftEval1: F de.ftEval1
              , publicEvals: PointEval
                  { zeta: F dummyWrapXhatZeta
                  , omegaTimesZeta: F dummyWrapXhatOmegaZeta
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
            , prevStepAcc: WeierstrassAffinePoint { x: F stepSgD.x, y: F stepSgD.y }
            , headPrevEvals
            , headSlotPrevWrapBpChalsVec:
                Vector.replicate @n (map F dummyIpaChallenges.wrapExpanded)
            }
        InductivePrev prevCp prevTag ->
          let
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            prevStepBpChalsExpanded :: Vector StepIPARounds StepField
            prevStepBpChalsExpanded =
              map
                ( \sc ->
                    toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                      stepEndoScalarF
                )
                prev.rawBulletproofChallenges

            prevWrapPI :: Array WrapField
            prevWrapPI = wrapPublicInput prevVerifier prevCp
          in
            -- Reference: OCaml `step_main`'s
            -- `messages_for_next_step_proof.old_bulletproof_challenges`
            -- threading.
            runExists
              ( \(CompiledProofWidthData wd) ->
                  let
                    -- FFI boundary: kimchi's `prev_challenges` argument
                    -- expects a flat `Array {sgX, sgY, challenges :: Array}`
                    -- of length PaddedLength=2. Build it from the
                    -- pre-padded Vectors via `Vector.zipWith`, then
                    -- convert to Array exactly once at the boundary.
                    -- (sgX/sgY are `Vesta.ScalarField = StepField` —
                    -- the Pallas point's coords live in Pallas's base
                    -- field, which equals Vesta's scalar field.)
                    prevWrapKimchiPrevChals
                      :: Array
                           { sgX :: StepField
                           , sgY :: StepField
                           , challenges :: Array WrapField
                           }
                    prevWrapKimchiPrevChals = Vector.toUnfoldable $
                      Vector.zipWith
                        ( \sg ch ->
                            { sgX: sg.x
                            , sgY: sg.y
                            , challenges: Vector.toUnfoldable ch
                            }
                        )
                        wd.outerStepChalPolyCommsPadded
                        wd.msgWrapChallengesPadded

                    prevWrapOracles =
                      ProofFFI.vestaProofOracles slotWrapVK
                        { proof: prev.wrapProof
                        , publicInput: prevWrapPI
                        , prevChallenges: prevWrapKimchiPrevChals
                        }

                    peWF = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
                    prevHeadPrevEvals = StepAllEvals
                      { ftEval1: F prevWrapOracles.ftEval1
                      , publicEvals: PointEval
                          { zeta: F prevWrapOracles.publicEvalZeta
                          , omegaTimesZeta: F prevWrapOracles.publicEvalZetaOmega
                          }
                      , zEvals: peWF (ProofFFI.proofZEvals prev.wrapProof)
                      , witnessEvals:
                          map peWF (ProofFFI.proofWitnessEvals prev.wrapProof)
                      , coeffEvals:
                          map peWF (ProofFFI.proofCoefficientEvals prev.wrapProof)
                      , sigmaEvals:
                          map peWF (ProofFFI.proofSigmaEvals prev.wrapProof)
                      , indexEvals:
                          map peWF (ProofFFI.proofIndexEvals prev.wrapProof)
                      }

                    -- Take the slot's `Vector n` view by dropping the
                    -- prepended dummies from the padded `Vector PaddedLength`.
                    headSlotPrevWrapBpChalsVec
                      :: Vector n (Vector WrapIPARounds (F WrapField))
                    headSlotPrevWrapBpChalsVec =
                      Vector.drop @slotPad
                        (map (map F) wd.msgWrapChallengesPadded)
                  in
                    { prevSg: prev.challengePolynomialCommitment
                    , prevStepChals: prevStepBpChalsExpanded
                    , prevStepAcc: WeierstrassAffinePoint
                        { x: F prev.challengePolynomialCommitment.x
                        , y: F prev.challengePolynomialCommitment.y
                        }
                    , headPrevEvals: prevHeadPrevEvals
                    , headSlotPrevWrapBpChalsVec
                    }
              )
              prev.widthData

      -- Recurse into rest.
      restSideInfo :: ShapeProveSideInfo restMpv
      restSideInfo =
        { challengePolynomialCommitments: tailChalPolyComms
        , unfinalizedSlots: tailUnfinalized
        , baseCaseWrapPublicInputs: tailBaseCaseWrapPIs
        }
      restProveData = shapeProveData @rest restCfg wrapCR restSideInfo restPrevs restVkCarrier
    in
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
          F (Curves.fromInt (slotWrapDomainLog2 - 13) :: WrapField)
            :< restProveData.prevWrapDomainIndices
      , kimchiPrevEntries:
          { sgX: headChalPolyComm.x
          , sgY: headChalPolyComm.y
          , challenges: msgForNextWrapRealChals
          } :< restProveData.kimchiPrevEntries
      , slotsValue:
          product slotData.headSlotPrevWrapBpChalsVec restProveData.slotsValue
      }

--------------------------------------------------------------------------------
-- CompilableSpec Slot SideLoaded (mpvMax ≥ 1, recursive)
--
-- Structural mirror of the `Slot Compiled` instance. The slot's wrap
-- VK / actual_wrap_domain / step_domain are sourced at runtime from
-- the head `VerificationKey` of the spec-indexed `vkCarrier`.
-- Reference: OCaml `step_main.ml:520-525`'s `Side_loaded -> of_side_loaded`.
--------------------------------------------------------------------------------

instance
  ( CompilableSpec rest restSlotVKs restPrevsCarrier restMpv restSlots restValCarrier restCarrier restVkCarrier restScaffolds
  -- Both orderings: `restMpv 1 mpv` synthesizes `mpv` from `restMpv`;
  -- `1 restMpv mpv` is the form `Vector.uncons` needs to recover
  -- `restMpv` from `mpv`.
  , Add restMpv 1 mpv
  , Add 1 restMpv mpv
  , Add pad mpv PaddedLength
  , Reflectable mpvMax Int
  , Reflectable mpv Int
  , Reflectable pad Int
  , Add slotPad mpvMax PaddedLength
  , Reflectable slotPad Int
  , Compare mpv 3 LT
  , Compare 0 mpv LT
  , Compare mpvMax 3 LT
  , CircuitType StepField prevHeadInput prevHeadInputVar
  , CircuitType StepField prevHeadOutput prevHeadOutputVar
  , SlotStatementsCarrier rest restValCarrier
  ) =>
  CompilableSpec
    (Slot SideLoaded mpvMax (StatementIO prevHeadInput prevHeadOutput) /\ rest)
    -- Side-loaded slots have NO compile-time wrap key; the head entry
    -- of `slotVKs` is `Unit`. Mirrors the `vkCarrier` head being
    -- `VerificationKey` (the runtime VK takes the place of the
    -- compile-time `SlotWrapKey`).
    (Unit /\ restSlotVKs)
    ( PrevSlot prevHeadInput mpvMax (StatementIO prevHeadInput prevHeadOutput) prevHeadOutput
        /\ restPrevsCarrier
    )
    mpv
    (Product (Vector mpvMax) restSlots)
    (StatementIO prevHeadInput prevHeadOutput /\ restValCarrier)
    ( Step.PerProofWitness
        mpvMax
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
        /\ restCarrier
    )
    (SideloadBundle.Bundle /\ restVkCarrier)
    -- Side-loaded blueprint = the per-domain lagrange tables (one
    -- entry per `wrap_domain ∈ {N0, N1, N2}`). The runtime VK is
    -- bundled in by `buildSlotVkSources` at circuit-build time.
    (SlotVkBlueprintSideLoaded /\ restScaffolds)
  where
  -- Structural mirror of the `Slot Compiled` `shapeCompileData`. The
  -- slot's compile-time `slotWrapDomainLog2` and `slotLagrange` are
  -- carried as placeholders so the `perSlotLagrangeAt` /
  -- `perSlotFopDomainLog2s` vectors still have the right shape; the
  -- side-loaded slot's actual wrap-domain / lagrange come from
  -- `headSlotVkSource = SideloadedExistsVk …` (one-hot multiplexed
  -- against the runtime VK's `actualWrapDomainSize` bits in
  -- `Step.Main`).
  shapeCompileData cfg selfStepDomainLog2s =
    let
      _ /\ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      restShape = shapeCompileData @rest restCfg selfStepDomainLog2s
      outerMpv = reflectType (Proxy @mpv)
      slotMpvMax = reflectType (Proxy @mpvMax)
      outerWrapDomainLog2 = case cfg.wrapDomainOverride of
        Just o -> o
        Nothing -> Dummy.wrapDomainLog2ForProofsVerified outerMpv

      -- Unused for side-loaded slots (Step.Main reads the per-domain
      -- triple inside `SideloadedExistsVk`); kept to match the
      -- `perSlotLagrangeAt` vector shape.
      slotWrapDomainLog2 = Dummy.wrapDomainLog2ForProofsVerified slotMpvMax
      slotLagrange =
        mkConstLagrangeBaseLookup \i ->
          coerce (ProofFFI.vestaSrsLagrangeCommitmentAt cfg.srs.pallasSrs slotWrapDomainLog2 i)

      -- Per-domain lagrange tables for the side-loaded VK's
      -- `actualWrapDomainSize` ∈ {N0=13, N1=14, N2=15}. Step.Main
      -- one-hot-muxes among these via `mkSideloadedLagrangeLookup`.
      sideloadedPerDomainLagrangeAts
        :: Vector ProofsVerifiedCount (Int -> AffinePoint (F StepField))
      sideloadedPerDomainLagrangeAts = map
        ( \log2 i ->
            coerce (ProofFFI.vestaSrsLagrangeCommitmentAt cfg.srs.pallasSrs log2 i)
        )
        (13 :< 14 :< 15 :< Vector.nil)

      outerBcd = Dummy.baseCaseDummies { maxProofsVerified: outerMpv }
      outerDummySgs = Dummy.computeDummySgValues outerBcd cfg.srs.pallasSrs cfg.srs.vestaSrs
    in
      { stepProveCtx:
          { srsData:
              { perSlotLagrangeAt:
                  slotLagrange :< restShape.stepProveCtx.srsData.perSlotLagrangeAt
              , blindingH:
                  coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs
              , perSlotFopDomainLog2s:
                  -- Side-loaded slots have no compile-time step domain;
                  -- placeholder fills the vector shape (real dispatch
                  -- is in `Step.FinalizeOtherProof`'s SideLoadedMode).
                  selfStepDomainLog2s
                    :< restShape.stepProveCtx.srsData.perSlotFopDomainLog2s
              , perSlotVkBlueprints:
                  sideloadedPerDomainLagrangeAts
                    /\ restShape.stepProveCtx.srsData.perSlotVkBlueprints
              }
          , dummySg: outerDummySgs.ipa.wrap.sg
          , crs: cfg.srs.vestaSrs
          , debug: cfg.debug
          }
      , wrapDomainLog2: outerWrapDomainLog2
      }

  -- Structural copy of the `Slot Compiled` `mkStepAdvice` with two
  -- changes:
  --   (1) per-slot witness sized at `mpvMax` (the side-loaded tag's
  --       compile-time upper bound); the runtime VK's
  --       `actualWrapDomainSize` ≤ `mpvMax` is masked in-circuit.
  --   (2) `slotParams` sourced from the runtime VK at the head of
  --       `vkCarrier`: `wrapVk` → kimchi `VerifierIndex`,
  --       `actualWrapDomainSize` → wrap-domain log2. The
  --       `slotStepDomainLog2` placeholder is consumed only at the
  --       BasePrev / dummy site (where `proofMustVerify = false`
  --       masks its downstream effect); InductivePrev reads the
  --       prev's own `stepDomainLog2`.
  mkStepAdvice cfg stepCR wrapCR appInput (headSlot /\ restPrevs) (headVk /\ restVkCarrier) = do
    let
      slotWrapVK = SideloadBundle.verifierIndex headVk
      slotMpvMax = reflectType (Proxy @mpvMax)
      _ /\ restSlotVKs = cfg.perSlotImportedVKs

      -- Decode `actualWrapDomainSize` from the VK descriptor's
      -- length-3 one-hot bool vector.
      SLVK.VerificationKey headVkRec = SideloadBundle.projectVk headVk
      headActualWrapDomainSize =
        boolVecToProofsVerified headVkRec.actualWrapDomainSize

      slotParams =
        { slotWrapVK
        , slotWrapDomainLog2:
            Dummy.wrapDomainLog2ForProofsVerified
              (fromEnum headActualWrapDomainSize)
        , slotStepDomainLog2:
            -- Side-loaded VKs don't carry the prev's step domain;
            -- the step circuit dispatches via Pseudo over [0..16] in
            -- `Step.FinalizeOtherProof`'s SideLoadedMode. This stand-
            -- in (= mpvMax-domain wrap log2) is consumed only at the
            -- BasePrev/dummy site, where `proofMustVerify=false`
            -- masks its downstream effect; InductivePrev reads
            -- `prev.stepDomainLog2`.
            Dummy.wrapDomainLog2ForProofsVerified slotMpvMax
        }

      bcd = Dummy.baseCaseDummies { maxProofsVerified: slotMpvMax }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      dummyWrapSg = dummySgs.ipa.wrap.sg
      dummyStepSg = dummySgs.ipa.step.sg

      proofsVerifiedMask :: Vector MaxProofsVerified Boolean
      proofsVerifiedMask =
        (slotMpvMax >= 2) :< (slotMpvMax >= 1) :< Vector.nil

      stepEndoScalarF :: StepField
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

            fopProofState = Dummy.stepDummyUnfinalizedProof @mpvMax bcd
              { domainLog2: Dummy.wrapDomainLog2ForProofsVerified slotMpvMax }
              (map SizedF.wrapF bcd.ipaStepChallenges)

            baseCaseWrapPI = dummyWrapTockPublicInput @mpvMax
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
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            prevStepBpChalsExpanded :: Vector StepIPARounds StepField
            prevStepBpChalsExpanded =
              map
                ( \sc ->
                    toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                      stepEndoScalarF
                )
                prev.rawBulletproofChallenges

            wrapPI :: Array WrapField
            wrapPI = wrapPublicInput prevVerifier prevCp
          in
            runExists
              ( \(CompiledProofWidthData wd) ->
                  let
                    prevZetaField :: StepField
                    prevZetaField =
                      coerce
                        (toFieldPure prev.rawPlonk.zeta (F prevVerifier.stepEndo))

                    prevStepGenerator :: StepField
                    prevStepGenerator = domainGenerator prev.stepDomainLog2

                    prevStepShifts :: Vector 7 StepField
                    prevStepShifts = domainShifts prev.stepDomainLog2

                    prevVanishesOnZk :: StepField
                    prevVanishesOnZk = ProofFFI.permutationVanishingPolynomial
                      { domainLog2: prev.stepDomainLog2
                      , zkRows: prevVerifier.stepZkRows
                      , pt: prevZetaField
                      }

                    prevDv = expandDeferredForVerify
                      { rawPlonk: prev.rawPlonk
                      , rawBulletproofChallenges: prev.rawBulletproofChallenges
                      , branchData: prev.branchData
                      , spongeDigestBeforeEvaluations:
                          prev.spongeDigestBeforeEvaluations
                      , allEvals: prev.prevEvals
                      , pEval0Chunks: prev.pEval0Chunks
                      , oldBulletproofChallenges: wd.oldBulletproofChallenges
                      , domainLog2: prev.stepDomainLog2
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
                      wd.outerStepChalPolyCommsPadded
                      wd.msgWrapChallengesPadded

                    prevPaddedWrapBpChals
                      :: Vector PaddedLength (Vector WrapIPARounds WrapField)
                    prevPaddedWrapBpChals = wd.msgWrapChallengesPadded

                    prevPaddedStepHashChals
                      :: Vector PaddedLength (Vector StepIPARounds StepField)
                    prevPaddedStepHashChals = wd.oldBulletproofChallengesPadded

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
                    { prevStatement: prev.statement
                    , stepOpeningSg: prev.challengePolynomialCommitment
                    , kimchiPrevSg: prev.challengePolynomialCommitment
                    , wrapProof: prev.wrapProof
                    , wrapPublicInputArr: wrapPI
                    , prevChalPolys: prevPaddedChalPolys
                    , wrapPlonkRaw:
                        { alpha: SizedF.unwrapF prevDv.plonk.alpha
                        , beta: SizedF.unwrapF prevDv.plonk.beta
                        , gamma: SizedF.unwrapF prevDv.plonk.gamma
                        , zeta: SizedF.unwrapF prevDv.plonk.zeta
                        }
                    , wrapPrevEvals: prev.prevEvals
                    , wrapBranchData: prev.branchData
                    , wrapSpongeDigest: prev.spongeDigestBeforeEvaluations
                    , mustVerify: true
                    , wrapOwnPaddedBpChals: prevPaddedWrapBpChals
                    , fopState
                    , stepAdvicePrevEvals: prev.prevEvals
                    , kimchiPrevChallengesExpanded: prevStepBpChalsExpanded
                    , prevChallengesForStepHash: prevPaddedStepHashChals
                    }
              )
              prev.widthData

    contrib <- buildSlotAdvice @mpvMax
      { publicInput: appInput
      , prevStatement: slotData.prevStatement
      , wrapDomainLog2: slotParams.slotWrapDomainLog2
      , stepDomainLog2: slotParams.slotStepDomainLog2
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

    let restCfg = cfg { perSlotImportedVKs = restSlotVKs }
    restResult <- mkStepAdvice @rest restCfg stepCR wrapCR appInput restPrevs restVkCarrier

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
        , wrapVerifierIndex: extractWrapVKCommsAdvice wrapCR.verifierIndex
        , kimchiPrevChallenges:
            contrib.slotKimchiPrevEntry :< restA.kimchiPrevChallenges
        , prevAppStates: slotData.prevStatement /\ restA.prevAppStates
        -- Side-loaded slot contributes the runtime VK supplied by the
        -- caller via the spec-indexed `vkCarrier`. Mirrors OCaml's
        -- per-prove `~handler` model: this is the channel through which
        -- `getSideloadedVKsCarrier` reads the runtime VK in the rule
        -- body. `headVk` was destructured at the start of this method.
        , sideloadedVKs: headVk /\ restA.sideloadedVKs
        }
    pure
      { stepAdvice: combinedAdvice
      , challengePolynomialCommitments:
          contrib.challengePolynomialCommitment :< restResult.challengePolynomialCommitments
      , baseCaseWrapPublicInputs:
          slotData.wrapPublicInputArr :< restResult.baseCaseWrapPublicInputs
      }

  -- Structural copy of the `Slot Compiled` `shapeProveData` body
  -- with the same three substitutions as `mkStepAdvice` above:
  -- slot sized at `mpvMax` (not `n`), `slotWrapVK` /
  -- `slotWrapDomainLog2` from the runtime VK, rest threaded with
  -- `restVkCarrier`. The `headSlotPrevWrapBpChalsVec :: Vector mpvMax`
  -- BasePrev branch is sized at the side-loaded tag's upper bound.
  shapeProveData cfg wrapCR sideInfo (headSlot /\ restPrevs) (headVk /\ restVkCarrier) =
    let
      _ /\ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      slotMpvMax = reflectType (Proxy @mpvMax)

      -- Decode actualWrapDomainSize from the bundle's `vk` descriptor;
      -- the runtime `verifierIndex` is the bundle's sibling half.
      SLVK.VerificationKey headVkRec = SideloadBundle.projectVk headVk
      headActualWrapDomainSize =
        boolVecToProofsVerified headVkRec.actualWrapDomainSize

      slotWrapVK = SideloadBundle.verifierIndex headVk

      slotWrapDomainLog2 :: Int
      slotWrapDomainLog2 =
        Dummy.wrapDomainLog2ForProofsVerified
          (fromEnum headActualWrapDomainSize)

      bcd = Dummy.baseCaseDummies { maxProofsVerified: slotMpvMax }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      wrapSgD = dummySgs.ipa.wrap.sg
      stepSgD = dummySgs.ipa.step.sg

      { head: PerProofUnfinalized headUnfRaw, tail: tailUnfinalized } =
        Vector.uncons sideInfo.unfinalizedSlots
      { head: headChalPolyComm, tail: tailChalPolyComms } =
        Vector.uncons sideInfo.challengePolynomialCommitments
      { head: headBaseCaseWrapPI, tail: tailBaseCaseWrapPIs } =
        Vector.uncons sideInfo.baseCaseWrapPublicInputs

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

      wrapEndoScalar :: WrapField
      wrapEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

      msgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      msgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField) wrapEndoScalar
          )
          headUnfRaw.bulletproofChallenges

      stepEndoScalarF :: StepField
      stepEndoScalarF =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

      slotData
        :: { prevSg :: AffinePoint WrapField
           , prevStepChals :: Vector StepIPARounds StepField
           , prevStepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
           , headPrevEvals :: StepAllEvals (F WrapField)
           , headSlotPrevWrapBpChalsVec :: Vector mpvMax (Vector WrapIPARounds (F WrapField))
           }
      slotData = case headSlot of
        BasePrev _ ->
          let
            baseCaseDummyChalPoly =
              { sg: wrapSgD, challenges: dummyIpaChallenges.wrapExpanded }
            toFFI r =
              { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
            dummyWrapOracles =
              ProofFFI.vestaProofOracles slotWrapVK
                { proof: dummyWrapProof bcd
                , publicInput: headBaseCaseWrapPI
                , prevChallenges: map toFFI [ baseCaseDummyChalPoly, baseCaseDummyChalPoly ]
                }
            dummyWrapXhatZeta = dummyWrapOracles.publicEvalZeta
            dummyWrapXhatOmegaZeta = dummyWrapOracles.publicEvalZetaOmega
            de = bcd.dummyEvals
            pe = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
            headPrevEvals = StepAllEvals
              { ftEval1: F de.ftEval1
              , publicEvals: PointEval
                  { zeta: F dummyWrapXhatZeta
                  , omegaTimesZeta: F dummyWrapXhatOmegaZeta
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
            , prevStepAcc: WeierstrassAffinePoint { x: F stepSgD.x, y: F stepSgD.y }
            , headPrevEvals
            , headSlotPrevWrapBpChalsVec:
                Vector.replicate @mpvMax (map F dummyIpaChallenges.wrapExpanded)
            }
        InductivePrev prevCp prevTag ->
          let
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            prevStepBpChalsExpanded :: Vector StepIPARounds StepField
            prevStepBpChalsExpanded =
              map
                ( \sc ->
                    toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                      stepEndoScalarF
                )
                prev.rawBulletproofChallenges

            prevWrapPI :: Array WrapField
            prevWrapPI = wrapPublicInput prevVerifier prevCp
          in
            runExists
              ( \(CompiledProofWidthData wd) ->
                  let
                    prevWrapKimchiPrevChals
                      :: Array
                           { sgX :: StepField
                           , sgY :: StepField
                           , challenges :: Array WrapField
                           }
                    prevWrapKimchiPrevChals = Vector.toUnfoldable $
                      Vector.zipWith
                        ( \sg ch ->
                            { sgX: sg.x
                            , sgY: sg.y
                            , challenges: Vector.toUnfoldable ch
                            }
                        )
                        wd.outerStepChalPolyCommsPadded
                        wd.msgWrapChallengesPadded

                    prevWrapOracles =
                      ProofFFI.vestaProofOracles slotWrapVK
                        { proof: prev.wrapProof
                        , publicInput: prevWrapPI
                        , prevChallenges: prevWrapKimchiPrevChals
                        }

                    peWF = coerce :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> PointEval (F WrapField)
                    prevHeadPrevEvals = StepAllEvals
                      { ftEval1: F prevWrapOracles.ftEval1
                      , publicEvals: PointEval
                          { zeta: F prevWrapOracles.publicEvalZeta
                          , omegaTimesZeta: F prevWrapOracles.publicEvalZetaOmega
                          }
                      , zEvals: peWF (ProofFFI.proofZEvals prev.wrapProof)
                      , witnessEvals:
                          map peWF (ProofFFI.proofWitnessEvals prev.wrapProof)
                      , coeffEvals:
                          map peWF (ProofFFI.proofCoefficientEvals prev.wrapProof)
                      , sigmaEvals:
                          map peWF (ProofFFI.proofSigmaEvals prev.wrapProof)
                      , indexEvals:
                          map peWF (ProofFFI.proofIndexEvals prev.wrapProof)
                      }

                    headSlotPrevWrapBpChalsVec
                      :: Vector mpvMax (Vector WrapIPARounds (F WrapField))
                    headSlotPrevWrapBpChalsVec =
                      Vector.drop @slotPad
                        (map (map F) wd.msgWrapChallengesPadded)
                  in
                    { prevSg: prev.challengePolynomialCommitment
                    , prevStepChals: prevStepBpChalsExpanded
                    , prevStepAcc: WeierstrassAffinePoint
                        { x: F prev.challengePolynomialCommitment.x
                        , y: F prev.challengePolynomialCommitment.y
                        }
                    , headPrevEvals: prevHeadPrevEvals
                    , headSlotPrevWrapBpChalsVec
                    }
              )
              prev.widthData

      restSideInfo :: ShapeProveSideInfo restMpv
      restSideInfo =
        { challengePolynomialCommitments: tailChalPolyComms
        , unfinalizedSlots: tailUnfinalized
        , baseCaseWrapPublicInputs: tailBaseCaseWrapPIs
        }
      restProveData = shapeProveData @rest restCfg wrapCR restSideInfo restPrevs restVkCarrier
    in
      { prevSgs: slotData.prevSg :< restProveData.prevSgs
      , prevStepChallenges:
          slotData.prevStepChals :< restProveData.prevStepChallenges
      , msgWrapChallenges:
          msgForNextWrapRealChals :< restProveData.msgWrapChallenges
      , prevUnfinalizedProofs: headUnfinalizedWrap :< restProveData.prevUnfinalizedProofs
      , prevStepAccs: slotData.prevStepAcc :< restProveData.prevStepAccs
      , prevEvals: slotData.headPrevEvals :< restProveData.prevEvals
      , prevWrapDomainIndices:
          F (Curves.fromInt (slotWrapDomainLog2 - 13) :: WrapField)
            :< restProveData.prevWrapDomainIndices
      , kimchiPrevEntries:
          { sgX: headChalPolyComm.x
          , sgY: headChalPolyComm.y
          , challenges: msgForNextWrapRealChals
          } :< restProveData.kimchiPrevEntries
      , slotsValue:
          product slotData.headSlotPrevWrapBpChalsVec restProveData.slotsValue
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
--   4. `slotVKs`     — that branch's per-slot imported-VK carrier.
--
-- All four vary per-branch. The shared types — `inputVal`, `outputVal`,
-- `prevInputVal` — live at the multi-branch level (they parameterize
-- the SHARED wrap VK's public-input layout), not in `RulesSpec`.
--------------------------------------------------------------------------------

-- | Kind: a type-level list of rule specs.
data RulesSpec

-- | Empty rules list. A multi-branch compile with `RulesNil` is
-- | structurally a no-op and is rejected at the API level (no
-- | `CompilableRulesSpecShape` instance for the empty list).
foreign import data RulesNil :: RulesSpec

-- | One branch's contribution to the rules list. The four type-level
-- | parameters bind that branch's mpv / valCarrier / prevsSpec /
-- | slotVKs; the fifth is the rest of the list.
foreign import data RulesCons :: Int -> Type -> Type -> Type -> RulesSpec -> RulesSpec

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
-- | per-rule `MpvPadding ruleMpv mpvPad mpvMax` constraint inside
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
  MaxOfRulesMpvs (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest) mpvMax

-- | Multi-branch compile config. Shape is shared across all branches;
-- | per-branch data lives in the value-level `rulesCarrier` argument
-- | passed alongside (a `Tuple` chain matching the `RulesSpec` shape).
type CompileMultiConfig =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , debug :: Boolean
  , wrapDomainOverride :: Maybe Int
  }

-- | Per-branch prover for ONE branch. Each `RulesCons` slot in the
-- | carrier corresponds to a `BranchProver` of that branch's shape.
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> Type -> (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier vkCarrier inputVal outputVal m =
  BranchProver
    ( StepInputs prevsSpec inputVal prevsCarrier vkCarrier
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
  -> (Type -> Type)
  -> Type
  -> Type
  -> Type
  -> Type
  -> Type
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
    slotsMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
  | rs topBranches ->
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
    slotsMax
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
-- | by `StepSlotsCarrier prevsSpec … carrier` (carrier from prevsSpec) and
-- | by Add chains (outputSize from mpv). These constraints feed back
-- | into the funDep `rs -> rulesCarrier` resolution.
instance
  ( CompilableRulesSpec rest inputVal outputVal prevInputVal
      topBranches
      restBranches
      mpvMax
      slotsMax
      restCarrier
      restStepCompileFns
      restCtxs
      restStepCompileResults
      restStepProveFns
  , Add restBranches 1 branches
  , StepSlotsCarrier
      prevsSpec
      StepIPARounds
      WrapIPARounds
      (F StepField)
      (Type2 (SplitField (F StepField) Boolean))
      Boolean
      ruleMpv
      carrier
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
    (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    slotsMax
    ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize slotVKs vkCarrier blueprints
        /\ restCarrier
    )
    ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> Effect PProveStep.StepCompileResult
      )
        /\ restStepCompileFns
    )
    (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
    (PProveStep.StepCompileResult /\ restStepCompileResults)
    ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> PProveStep.StepCompileResult
        -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
             inputVal
             ruleMpv
             carrier
             valCarrier
             vkCarrier
        -> ExceptT EvaluationError Effect
             (PProveStep.StepProveResult outputSize)
      )
        /\ restStepProveFns
    )
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
      @slotsMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      (Proxy :: Proxy rest)
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
        @slotsMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
        rest
  runStepCompiles (ctx /\ restCtxs) (RuleEntry r /\ restEntries) = do
    headResult <- r.stepCompileFn ctx
    tailResults <- runStepCompiles
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @slotsMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      restCtxs
      restEntries
    pure (headResult /\ tailResults)
  buildWrapPerBranchVec (headResult /\ restResults) =
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
        @topBranches
        @restBranches
        @mpvMax
        @slotsMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
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
        @slotsMax
        @restCarrier
        @restStepCompileFns
        @restCtxs
        @restStepCompileResults
        @restStepProveFns
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
  CompilableRulesSpec rs inputVal outputVal prevInputVal topBranches branches mpvMax slotsMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier <=
  CompilableRulesSpecShape
    rs
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    slotsMax
    rulesCarrier
    stepCompileFnsCarrier
    perBranchCtxsCarrier
    perBranchStepCompileResults
    stepProveFnsCarrier
    proversCarrier
  | rs topBranches -> branches mpvMax rulesCarrier stepCompileFnsCarrier perBranchCtxsCarrier
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
    :: CompileMultiConfig
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
    :: CompileMultiConfig
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
  :: forall @rs @inputVal @outputVal @prevInputVal @topBranches @mpvMax @slotsMax
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
       slotsMax
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
  => Reflectable topBranches Int
  => CompileMultiConfig
  -> rulesCarrier
  -> Effect
       { stepResults :: perBranchStepCompileResults
       , log2s :: Vector topBranches Int
       }
runMultiCompileFull cfg rules = do
  let
    placeholder :: Vector topBranches Int
    placeholder = Vector.replicate roughDomainsLog2
  log2s <- prePassDomainLog2s
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @topBranches
    @topBranches
    @mpvMax
    @slotsMax
    @rulesCarrier
    @stepCompileFnsCarrier
    @perBranchCtxsCarrier
    @perBranchStepCompileResults
    @stepProveFnsCarrier
    @proversCarrier
    cfg
    placeholder
    rules
  stepResults <- runMultiCompile
    @rs
    @inputVal
    @outputVal
    @prevInputVal
    @topBranches
    @topBranches
    @mpvMax
    @slotsMax
    @rulesCarrier
    @stepCompileFnsCarrier
    @perBranchCtxsCarrier
    @perBranchStepCompileResults
    @stepProveFnsCarrier
    @proversCarrier
    cfg
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
    slotsMax
    Unit
    Unit
    Unit
    Unit
    Unit
    Unit
  where
  prePassDomainLog2s _ _ _ = pure Vector.nil
  runMultiCompile _ _ _ = pure unit
  buildBranchProvers _ _ _ _ _ _ _ = pure unit

instance
  ( CompilableRulesSpecShape rest inputVal outputVal prevInputVal
      topBranches
      restBranches
      mpvMax
      slotsMax
      restCarrier
      restStepCompileFns
      restCtxs
      restStepCompileResults
      restStepProveFns
      restProvers
  , CompilableSpec prevsSpec slotVKs prevsCarrier ruleMpv slots valCarrier
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
  , MpvPadding.MpvPadding mpvPad ruleMpv mpvMax
  , Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  , Add unfsTotal 1 digestPlusUnfs
  , Add digestPlusUnfs mpvMax outputSize
  , PadSlots slots ruleMpv
  -- Wrap-stage constraints on `mpvMax`/`slotsMax` (the wrap circuit's
  -- wider shape). The general `PadProveDataMpv` instance front-pads the
  -- per-rule `ruleMpv`/`slots` shape up to `mpvMax`/`slotsMax`.
  , Reflectable mpvMax Int
  , Reflectable padMax Int
  , Add padMax mpvMax PaddedLength
  , Compare mpvMax 3 LT
  , Add mpvMax Wrap.IvpBaseline totalBasesMax
  , Add 1 totalBasesMaxPred totalBasesMax
  , PadSlots slotsMax mpvMax
  , PadProveDataMpv ruleMpv slots mpvMax slotsMax
  -- `topBranches` stays fixed across the recursion; required by
  -- `buildStepProveCtx` and Vector dispatch.
  , Reflectable topBranches Int
  , Compare 0 topBranches LT
  , Add 1 topBranchesPred topBranches
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
      inputVal
      outputVal
      prevInputVal
      topBranches
      branches
      mpvMax
      slotsMax
      ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize slotVKs vkCarrier blueprints
          /\ restCarrier
      )
      ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
          -> Effect PProveStep.StepCompileResult
        )
          /\ restStepCompileFns
      )
      (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
      (PProveStep.StepCompileResult /\ restStepCompileResults)
      ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
          -> PProveStep.StepCompileResult
          -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
               inputVal
               ruleMpv
               carrier
               valCarrier
               vkCarrier
          -> ExceptT EvaluationError Effect
               (PProveStep.StepProveResult outputSize)
        )
          /\ restStepProveFns
      )
  , Add 1 restBranches branches
  -- `Vector.cons` (`(:<)`) needs `Add n 1 nInc`; here n=restBranches,
  -- nInc=branches. PS doesn't commute `Add` automatically, so we
  -- supply both directions.
  , Add restBranches 1 branches
  ) =>
  CompilableRulesSpecShape
    (RulesCons ruleMpv valCarrier prevsSpec slotVKs rest)
    inputVal
    outputVal
    prevInputVal
    topBranches
    branches
    mpvMax
    slotsMax
    ( RuleEntry prevsSpec ruleMpv topBranches valCarrier inputVal carrier outputSize slotVKs vkCarrier blueprints
        /\ restCarrier
    )
    ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> Effect PProveStep.StepCompileResult
      )
        /\ restStepCompileFns
    )
    (PProveStep.StepProveContext ruleMpv topBranches blueprints /\ restCtxs)
    (PProveStep.StepCompileResult /\ restStepCompileResults)
    ( ( PProveStep.StepProveContext ruleMpv topBranches blueprints
        -> PProveStep.StepCompileResult
        -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
             inputVal
             ruleMpv
             carrier
             valCarrier
             vkCarrier
        -> ExceptT EvaluationError Effect
             (PProveStep.StepProveResult outputSize)
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
    ( BranchProver prevsSpec mpvMax prevsCarrier vkCarrier inputVal outputVal Effect
        /\ restProvers
    )
  where
  prePassDomainLog2s cfg placeholder (RuleEntry r /\ restEntries) = do
    let placeholderCtx = buildStepProveCtx @prevsSpec cfg r.slotVKs placeholder
    headLog2 <- r.preComputeStepDomainLog2Fn placeholderCtx
    restVec <- prePassDomainLog2s
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @slotsMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
      cfg
      placeholder
      restEntries
    pure (headLog2 :< restVec)
  runMultiCompile cfg log2s (RuleEntry r /\ restEntries) = do
    let ctx = buildStepProveCtx @prevsSpec cfg r.slotVKs log2s
    headResult <- r.stepCompileFn ctx
    tailResults <- runMultiCompile
      @rest
      @inputVal
      @outputVal
      @prevInputVal
      @topBranches
      @restBranches
      @mpvMax
      @slotsMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
      cfg
      log2s
      restEntries
    pure (headResult /\ tailResults)
  buildBranchProvers
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
          @topBranches
          -- Pass the wrap circuit's `mpvMax`/`slotsMax`. When
          -- `ruleMpv = mpvMax`, the identity `PadProveDataMpv`
          -- instance fires; otherwise the general instance front-pads
          -- the per-rule proveData up to the wrap circuit's wider
          -- shape via `Dummy.*` values.
          @mpvMax
          @slotsMax
          @mpvPad
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
      @slotsMax
      @restCarrier
      @restStepCompileFns
      @restCtxs
      @restStepCompileResults
      @restStepProveFns
      @restProvers
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
  -> Type
  -> Type
data RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize slotVKs vkCarrier blueprints = RuleEntry
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
      PProveStep.StepProveContext mpv nd blueprints -> Effect Int
  , stepCompileFn ::
      PProveStep.StepProveContext mpv nd blueprints -> Effect PProveStep.StepCompileResult
  -- | `vkCarrier` is the spec-derived per-slot side-loaded VK carrier
  -- | (`SideloadedVKsCarrier prevsSpec vkCarrier`): compiled slots
  -- | contribute `Unit`, side-loaded slots contribute a runtime
  -- | `Pickles.Sideload.VerificationKey`. Threaded explicitly here
  -- | because PS rejects rank-2 polymorphic record fields — pinning
  -- | it as a `RuleEntry` parameter lets the closure body's
  -- | `stepSolveAndProve` see a saturated `StepAdvice`.
  , stepProveFn ::
      PProveStep.StepProveContext mpv nd blueprints
      -> PProveStep.StepCompileResult
      -> PProveStep.StepAdvice prevsSpec StepIPARounds WrapIPARounds
           inputVal
           mpv
           carrier
           valCarrier
           vkCarrier
      -> ExceptT EvaluationError Effect (PProveStep.StepProveResult outputSize)
  , slotVKs :: slotVKs
  }

-- | Smart constructor: takes the user's rank-2 `StepRule` value and
-- | produces a `RuleEntry` with closures capturing it. Each closure's
-- | body invokes the captured rule against `stepCompile` /
-- | `stepSolveAndProve`.
mkRuleEntry
  :: forall @mpvMax @outputVal @prevInputVal
       prevsSpec mpv mpvPad nd ndPred outputSize valCarrier
       inputVal inputVar outputVar prevInputVar slotVKs
       carrier carrierVar pad unfsTotal digestPlusUnfs
       compileSideloadedVkCarrier sideloadedVkCarrier blueprints
   . CircuitGateConstructor StepField VestaG
  -- Compile-path carrier: cells = side-loaded VK descriptor. Synthesised
  -- by `MkUnitVkCarrier` for the `getSideloadedVKsCarrier` Effect
  -- instance inside `stepCompile` / `preComputeStepDomainLog2`.
  => BuildSlotVkSources (SLVK.VerificationKey (F StepField) Boolean) prevsSpec mpv blueprints compileSideloadedVkCarrier
  => MkUnitVkCarrier prevsSpec compileSideloadedVkCarrier
  -- Prove-path carrier: cells = `SideloadBundle.Bundle`. Sourced from
  -- `StepAdvice.sideloadedVKs` inside `stepSolveAndProve`.
  => BuildSlotVkSources SideloadBundle.Bundle prevsSpec mpv blueprints sideloadedVkCarrier
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
  => MpvPadding.MpvPadding mpvPad mpv mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => StepSlotsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
  => StepSlotsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => SlotStatementsCarrier prevsSpec valCarrier
  => PStepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> slotVKs
  -> Effect (RuleEntry prevsSpec mpv nd valCarrier inputVal carrier outputSize slotVKs sideloadedVkCarrier blueprints)
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

-- Type synonym for `StepRule`, used to avoid an import-cycle in the
-- `RuleEntry` field types.
type PStepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar =
  PProveStep.StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar

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
  :: forall @prevsSpec @nd ndPred slotVKs prevsCarrier mpv slots valCarrier carrier vkCarrier blueprints
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier vkCarrier blueprints
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => CompileMultiConfig
  -> slotVKs
  -> Vector nd Int
  -> PProveStep.StepProveContext mpv nd blueprints
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
-- runMultiProverBody — per-branch prover body.
--
-- Pipeline (mirrors single-rule runProverBody):
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
  :: forall @prevsSpec slotVKs prevsCarrier @mpv @slots @valCarrier @carrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
       @topBranches
       @mpvMax @slotsMax @mpvPad
       branches branchesPred topBranchesPred
       pad unfsTotal digestPlusUnfs outputSize carrierFVar
       padMax totalBasesMax totalBasesMaxPred
       vkCarrier blueprints
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier vkCarrier blueprints
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
  => MpvPadding.MpvPadding mpvPad mpv mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
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
  => Add mpvMax Wrap.IvpBaseline totalBasesMax
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
  -> Vector topBranches Int
  -- ^ FULL Vector of all branches' step domain log2s. Threaded
  --   to `buildStepProveCtx` so this rule's `finalizeOtherProofCircuit`
  --   has the multi-domain Pseudo dispatch table for Self-prev slots.
  --   Mirrors OCaml `compile.ml:568`'s `~step_domains:all_step_domains`.
  -> PProveStep.StepCompileResult
  -- ^ this branch's step compile result
  -> Int
  -- ^ this branch's selfStepDomainLog2 (from the pre-pass)
  -> RuleEntry prevsSpec mpv topBranches valCarrier inputVal carrier outputSize slotVKs vkCarrier blueprints
  -> StepInputs prevsSpec inputVal prevsCarrier vkCarrier
  -> ExceptT ProveError Effect
       (CompiledProof mpvMax (StatementIO inputVal outputVal) outputVal Unit)
runMultiProverBody
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
      , wrapDomainOverride: cfg.wrapDomainOverride
      }
    -- Pass the FULL `Vector topBranches Int` of all branches' step
    -- domain log2s. Drives multi-domain Pseudo dispatch in
    -- `finalizeOtherProofCircuit` for Self-prev slots — mirrors OCaml
    -- step_main's `step_domains:all_step_domains` (compile.ml:568).
    shape = shapeCompileData @prevsSpec perRuleCfg allStepDomainLog2s

  -- Per-prove side-loaded VK carrier from `stepInputs`. For
  -- compiled-only specs the caller passes `mkUnitVkCarrier @prevsSpec`
  -- (an all-Unit chain — semantically identical to the prior
  -- baked-in synthesis). For specs containing
  -- `Slot SideLoaded`, the caller supplies the runtime VK at
  -- the corresponding slot positions, mirroring OCaml's `~handler`.
  { stepAdvice, challengePolynomialCommitments, baseCaseWrapPublicInputs } <-
    liftEffect $ mkStepAdvice @prevsSpec perRuleCfg stepCR wrapResult appInput
      prevs
      sideloadedVKs

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
      sideloadedVKs

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
    -- FFI-shaped `prevChallenges` for the step proof's oracles.
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

    outerMpv = reflectType (Proxy @mpv)

    proofsVerifiedMask :: Vector MaxProofsVerified Boolean
    proofsVerifiedMask = (outerMpv >= 2) :< (outerMpv >= 1) :< Vector.nil

    wrapDvInput :: WrapDeferredValuesInput mpv
    wrapDvInput =
      { proof: stepResult.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: stepResult.publicInputs
      , allEvals
      , pEval0Chunks: [ stepOracles.publicEvalZeta ]
      , domainLog2: selfStepDomainLog2
      , zkRows
      , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
      , generator: (domainGenerator selfStepDomainLog2 :: StepField)
      , shifts: (domainShifts selfStepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: permutationVanishingPolynomial
          { domainLog2: selfStepDomainLog2
          , zkRows
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
    msgStep :: StepField
    msgStep =
      let
        F f = Vector.index stepResult.publicOutputs
          (unsafeFinite @outputSize (outerMpvMax * 32))
      in
        f

    stepProofSg :: AffinePoint WrapField
    stepProofSg = pallasProofOpeningSg stepResult.proof

    dummyWrapExpanded :: Vector WrapIPARounds WrapField
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
      { sgX: dummyWrapSgInStepField.x
      , sgY: dummyWrapSgInStepField.y
      , challenges: dummyIpaChallenges.wrapExpanded
      }

    msgWrapPadded :: Vector PaddedLength (Vector WrapIPARounds WrapField)
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

    msgWrap :: WrapField
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
      , advice: buildWrapAdvice
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
      , kimchiPrevChallenges: kimchiPrevPadded
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

  let
    widthData :: SomeCompiledProofWidthData
    widthData = mkSomeCompiledProofWidthData @mpv @pad
      { oldBulletproofChallenges: proveData.prevStepChallenges
      , msgWrapChallenges: proveData.msgWrapChallenges
      , outerStepChalPolyComms:
          map (\e -> { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
      , wrapDvInput
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
    , challengePolynomialCommitment: stepProofSg
    , messagesForNextStepProofDigest: msgStep
    , messagesForNextWrapProofDigest: msgWrap
    , widthData
    , stepDomainLog2: selfStepDomainLog2
    , wrapDv
    }

compileMulti
  :: forall @rs @outputVal @prevInputVal @slots
       inputVal mpvMax
       branches
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
       branchesPred totalBases totalBasesPred
   . CompilableRulesSpecShape rs inputVal outputVal prevInputVal
       branches
       branches
       mpvMax
       slots
       rulesCarrier
       stepCompileFnsCarrier
       perBranchCtxsCarrier
       perBranchStepCompileResults
       stepProveFnsCarrier
       proversCarrier
  => CircuitGateConstructor WrapField PallasG
  => Reflectable branches Int
  => Reflectable mpvMax Int
  => Add 1 branchesPred branches
  => Compare 0 branches LT
  => Compare mpvMax 3 LT
  => Add mpvMax Wrap.IvpBaseline totalBases
  => Add 1 totalBasesPred totalBases
  => PadSlots slots mpvMax
  -- Strict-equality enforcement: `mpvMax = max(ruleMpv across rs)`,
  -- not just `≥` (which the per-rule `MpvPadding` constraints inside
  -- `CompilableRulesSpecShape` already provide). Mirrors OCaml's
  -- `compile_promise ~max_proofs_verified:(module Nat.NX)` where X is
  -- the actual max across rules' prev counts.
  => MaxOfRulesMpvs rs mpvMax
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
    @slots
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