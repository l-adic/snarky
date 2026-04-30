-- | Top-level user-facing Pickles `compile` API.
-- |
-- | Wraps `Pickles.Prove.Step` / `Pickles.Prove.Wrap` into a single
-- | `compile` call that returns a `Prover` (with `step`), a `Verifier`,
-- | and the VK bundle downstream compiles consume as
-- | `perSlotImportedVKs` when using this Prover as a prev.
-- |
-- | Mirrors OCaml `Pickles.compile_promise` at a high level, modulo
-- | the advice-monad model difference (PS uses `CircuitM t m`
-- | polymorphism; OCaml dispatches via request/handler).
-- |
-- | Phased implementation — see
-- | `docs/pickles-compile-prover-api-plan.md`. `compile`'s body is
-- | shape-polymorphic: everything that differs between
-- | `PrevsSpecNil` / `PrevsSpecCons` shapes lives inside
-- | `CompilableSpec` class instances, which `compile` dispatches
-- | through. Phase 1 ships the `PrevsSpecNil` instance only;
-- | Phases 2/3 add `PrevsSpecCons` cases without touching `compile`.
module Pickles.Prove.Compile
  ( CompileConfig
  , CompileOutput
  , Prover
  , ProverVKs
  , ProveError
  , PrevSlot(..)
  , SlotWrapKey(..)
  , ShapeCompileData
  , ShapeProveData
  , ShapeProveSideInfo
  , StepInputs
  , Tag(..)
  , class CompilableSpec
  , class ConvertSlots
  , convertSlots
  , class PadProveDataMpv
  , PadProveDataDummies
  , padShapeProveData
  , mkStepAdvice
  , runCompile
  , shapeCompileData
  , shapeProveData
  , compile
  , module Pickles.Prove.Verify
  ) where

import Prelude

import Control.Monad.Except (ExceptT)
import Data.Array as Array
import Data.Exists (runExists)
import Data.Functor.Product (Product, product)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, over)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy as Dummy
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
  , vestaProofOracles
  , vestaSrsBlindingGenerator
  , vestaSrsLagrangeCommitmentAt
  ) as ProofFFI
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
  , StepRule
  , buildSlotAdvice
  , buildStepAdvice
  , dummyWrapTockPublicInput
  , extractWrapVKCommsAdvice
  , mkDummyMsgWrapHash
  , mkDummyPerProofUnfinalized
  , preComputeStepDomainLog2
  , stepCompile
  , stepSolveAndProve
  )
import Pickles.Prove.Verify
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
import Pickles.Prove.Wrap
  ( WrapCompileResult
  , buildWrapAdvice
  , buildWrapMainConfig
  , wrapCompile
  , wrapSolveAndProve
  )
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Main as PStepMain
import Pickles.Step.Prevs (class PrevValuesCarrier, class PrevsCarrier, PrevsSpecCons, PrevsSpecNil, StepSlot)
import Pickles.Types
  ( PaddedLength
  , PerProofUnfinalized(..)
  , PointEval(..)
  , StatementIO(..)
  , StepAllEvals(..)
  , StepField
  , StepIPARounds
  , WrapField
  , WrapIPARounds
  )
import Pickles.Util.Unique (Unique, newUnique)
import Pickles.Verify.Types (toPlonkMinimal)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (class PadSlots, NoSlots, noSlots, replicateSlots)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF (unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (fromShifted, toShifted) as Kimchi
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Types (class CircuitType, BoolVar, fieldsToValue)
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

type StepInputs :: Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier =
  { appInput :: inputVal
  , prevs :: prevsCarrier
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

-- | The prover closure returned by `compile`. `auxVal` is fixed to
-- | `Unit` because PS `StepRule` doesn't track auxiliary outputs.
type Prover
  :: Type -> Int -> Type -> Type -> Type -> Type -> (Type -> Type) -> Type
type Prover prevsSpec mpv inputVal outputVal stmtVal prevsCarrier m =
  { step ::
      StepInputs prevsSpec inputVal prevsCarrier
      -> ExceptT ProveError m (CompiledProof mpv stmtVal outputVal Unit)
  }

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

type CompileOutput
  :: Type -> Int -> Type -> Type -> Type -> Type -> (Type -> Type) -> Type
type CompileOutput prevsSpec mpv inputVal outputVal stmtVal prevsCarrier m =
  { prover :: Prover prevsSpec mpv inputVal outputVal stmtVal prevsCarrier m
  , tag :: Tag inputVal outputVal mpv
  , vks :: ProverVKs
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
type ShapeCompileData :: Int -> Int -> (Type -> Type) -> Type
type ShapeCompileData mpv nd slots =
  { stepProveCtx :: StepProveContext mpv nd
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
-- Phase 2b.31b step (a): identity instance only (fast path).
-- Phase 2b.31b step (b): general instance using `PadProveDataDummies`
-- + `ConvertSlots` to front-pad each Vector field and convert the
-- slots carrier.
--
-- The two-instance chain uses `else instance` (PS overlapping-instance
-- syntax). PS picks the first matching instance, so the identity head
-- with repeated vars (`mpv slots mpv slots`) fires whenever the types
-- align — which they do for every single-rule caller (NRR, Tree, both
-- per-branch SimpleChain rules) because `mpv = mpvMax` and
-- `slots = slotsMax`.
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
  :: Type -> Type -> Type -> Int -> (Type -> Type) -> Type -> Type -> Constraint
class
  CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  | prevsSpec -> slotVKs prevsCarrier mpv slots valCarrier carrier
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
    :: forall @nd _nd
     . Add 1 _nd nd
    => Compare 0 nd LT
    => Reflectable nd Int
    => CompileConfig prevsSpec slotVKs
    -> Vector nd Int
    -> ShapeCompileData mpv nd slots

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
    -> Effect
         { stepAdvice ::
             StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal mpv
               carrier
               valCarrier
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
    -> ShapeProveData mpv slots

--------------------------------------------------------------------------------
-- compile — shape-polymorphic entry point
--------------------------------------------------------------------------------

-- | Compile a Pickles rule into a `Prover` + `Verifier` + VK bundle.
-- |
-- | `rule` is passed as a direct argument (not through `CompileConfig`)
-- | because its type is polymorphic (`forall t m'. CircuitM ... => ...`)
-- | and PS record field access can't preserve the forall/constraints.
compile
  :: forall @prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
       @inputVal inputVar @outputVal outputVar @prevInputVal prevInputVar @m
       pad unfinalizedFieldsTotal digestPlusUnfs outputSize carrierFVar
       totalIpaCommitmentBases totalIpaCommitmentBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfinalizedFieldsTotal
  => Add unfinalizedFieldsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalIpaCommitmentBases
  => Add 1 totalIpaCommitmentBasesPred totalIpaCommitmentBases
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => CheckedType StepField (KimchiConstraint StepField) carrierFVar
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CompileConfig prevsSpec slotVKs
  -> StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> Effect
       ( CompileOutput prevsSpec mpv inputVal outputVal
           (StatementIO inputVal outputVal)
           prevsCarrier
           m
       )
compile cfg rule = runCompile
  @prevsSpec
  @inputVal
  @outputVal
  @prevInputVal
  @m
  cfg
  rule

--------------------------------------------------------------------------------
-- CompilableSpec PrevsSpecNil (N=0, NRR-shape)
--------------------------------------------------------------------------------

instance CompilableSpec PrevsSpecNil Unit Unit 0 NoSlots Unit Unit where
  shapeCompileData cfg _selfStepDomainLog2 =
    let
      bcd = Dummy.baseCaseDummies { maxProofsVerified: 0 }
    in
      { stepProveCtx:
          { srsData:
              { perSlotLagrangeAt: Vector.nil
              , blindingH:
                  (coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs)
                    :: AffinePoint (F StepField)
              , perSlotFopDomainLog2s: Vector.nil
              , perSlotKnownWrapKeys: Vector.nil
              -- Phase 2b.31a: mpvMax-padding dummies. Wrapped in
              -- `Unit ->` thunks so the (Rust-FFI-using)
              -- computeDummySgValues call inside mkDummyMsgWrapHash
              -- only fires when mpvFrontPad actually needs the dummy
              -- (i.e., mpvPad > 0). Single-rule callers have
              -- mpvPad = 0 so the thunks never fire — preserves
              -- byte-identical witness with the pre-Phase-2b.31a
              -- chacha8 RNG state.
              , dummyUnfp: \_ ->
                  PStepMain.liftDummyPerProofUnfinalized
                    (mkDummyPerProofUnfinalized bcd)
              }
          , dummySg: nrrDummyWrapSg cfg.srs.pallasSrs cfg.srs.vestaSrs
          , crs: cfg.srs.vestaSrs
          , debug: cfg.debug
          }
      , wrapDomainLog2: 13
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

  mkStepAdvice cfg _ wrapCR appInput _ =
    let
      -- Nil has no prev slots, so `stepDomainLog2` is dead — the
      -- per-slot dummy that consumes it gets replicated to a
      -- `Vector 0` (= empty). `0` is a sentinel; any value works.
      StepAdvice base = buildStepAdvice @PrevsSpecNil
        { publicInput: appInput
        , stepDomainLog2: 0
        , prevAppStates: unit
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

  shapeProveData _ _ _ _ =
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
-- CompilableSpec PrevsSpecCons (N ≥ 1, recursive)
--------------------------------------------------------------------------------

-- | Recursive instance covering all `PrevsSpecCons n stmt rest` shapes
-- | (homogeneous: Simple_chain; heterogeneous: Tree). Derives `mpv`,
-- | `prevsCarrier`, and `slots` by recursing through `rest`.
-- |
-- | Each slot's prev is a `PrevSlot` sum: `BasePrev` carries the
-- | user-supplied dummy input for proof-level base case (b0);
-- | `InductivePrev` carries a real `CompiledProof` from a previous
-- | `prover.step` for inductive cases (b1+).
-- |
-- | Phase 2: method bodies are stubs — type-level scaffolding only.
-- | Recursive Cons instance — head slot's per-slot data lives at
-- | the `Tuple` head; recursion threads the rest.
-- |
-- | This instance only fully implements the **single-slot Self**
-- | case (Simple_chain shape: rest = PrevsSpecNil, head slot = Self).
-- | Phase A: the type-level shape is generalized — `slotVKs` is
-- | `Tuple SlotWrapKey restSlotVKs`, `valCarrier` is `Tuple stmt
-- | restValCarrier`. Phase B (per-slot advice + combiner) wires
-- | `External` slot dispatch and arbitrary-rest support; until then
-- | the body crashes with a TODO if anything other than Self is
-- | reached, or rest is not PrevsSpecNil.
instance
  ( CompilableSpec rest restSlotVKs restPrevsCarrier restMpv restSlots restValCarrier restCarrier
  , Add restMpv 1 mpv
  , Add 1 restMpv mpv
  , Add pad mpv PaddedLength
  , Reflectable n Int
  , Reflectable mpv Int
  , Reflectable pad Int
  -- Per-slot pad (= PaddedLength − n), required by `buildSlotAdvice`'s
  -- Vector.drop @slotPad to extract this slot's prev_challenge
  -- _polynomial_commitments. Distinct from `pad` above (= PaddedLength
  -- − mpv) when n ≠ mpv (= heterogeneous shapes like Tree slot 0).
  , Add slotPad n PaddedLength
  , Reflectable slotPad Int
  , Compare mpv 3 LT
  , Compare 0 mpv LT
  , Compare n 3 LT
  , CircuitType StepField prevHeadInput prevHeadInputVar
  , CircuitType StepField prevHeadOutput prevHeadOutputVar
  , PrevValuesCarrier rest restValCarrier
  ) =>
  CompilableSpec
    (PrevsSpecCons n (StatementIO prevHeadInput prevHeadOutput) rest)
    (Tuple SlotWrapKey restSlotVKs)
    ( Tuple
        (PrevSlot prevHeadInput n (StatementIO prevHeadInput prevHeadOutput) prevHeadOutput)
        restPrevsCarrier
    )
    mpv
    (Product (Vector n) restSlots)
    (Tuple (StatementIO prevHeadInput prevHeadOutput) restValCarrier)
    ( Tuple
        ( StepSlot
            n
            StepIPARounds
            WrapIPARounds
            (F StepField)
            (Type2 (SplitField (F StepField) Boolean))
            Boolean
        )
        restCarrier
    )
  where
  shapeCompileData cfg selfStepDomainLog2s =
    let
      Tuple headSlotWrapKey restSlotVKs = cfg.perSlotImportedVKs
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
          (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt cfg.srs.pallasSrs slotWrapDomainLog2 i))
            :: AffinePoint (F StepField)

      outerBcd = Dummy.baseCaseDummies { maxProofsVerified: outerMpv }
      outerDummySgs = Dummy.computeDummySgValues outerBcd cfg.srs.pallasSrs cfg.srs.vestaSrs

      -- Self → Nothing (wrap VK comes from advice via Req.Wrap_index
      -- at prove time). External → Just (extracted external VK
      -- commitments). Mirrors OCaml step_main.ml:514-528 dispatch on
      -- Type_equal.Id.same_witness self.id tag.id.
      headKnownWrapKey =
        case headSlotWrapKey of
          Self -> Nothing
          External vks -> Just (extractWrapVKCommsAdvice vks.wrapCompileResult.verifierIndex)
    in
      { stepProveCtx:
          { srsData:
              { perSlotLagrangeAt:
                  slotLagrange :< restShape.stepProveCtx.srsData.perSlotLagrangeAt
              , blindingH:
                  (coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs)
                    :: AffinePoint (F StepField)
              , perSlotFopDomainLog2s:
                  slotFopDomainLog2s
                    :< restShape.stepProveCtx.srsData.perSlotFopDomainLog2s
              , perSlotKnownWrapKeys:
                  headKnownWrapKey :< restShape.stepProveCtx.srsData.perSlotKnownWrapKeys
              -- Phase 2b.31a: mpvMax-padding dummies (thunks; see
              -- Nil instance for rationale).
              , dummyUnfp: \_ ->
                  PStepMain.liftDummyPerProofUnfinalized
                    (mkDummyPerProofUnfinalized outerBcd)
              }
          , dummySg: outerDummySgs.ipa.wrap.sg
          , crs: cfg.srs.vestaSrs
          , debug: cfg.debug
          }
      , wrapDomainLog2: outerWrapDomainLog2
      }

  mkStepAdvice cfg stepCR wrapCR appInput (Tuple headSlot restPrevs) = do
    let
      slotN = reflectType (Proxy @n)
      Tuple headSlotWrapKey _ = cfg.perSlotImportedVKs

      -- Per-slot params (PS analog of OCaml `step.ml:751-754` Self/External
      -- dispatch). `Self` slots use the OUTER rule's compile artifacts
      -- (`stepCR` / `wrapCR`); `External` slots use the imported VKs.
      -- For `Self`: `wrapDomainLog2` honours `cfg.wrapDomainOverride`
      -- (mirrors OCaml `override_wrap_domain`). `External`: imported
      -- rule's wrapDomainLog2 already encodes its own override.
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

      -- Slot-specific dummies sized by THIS slot's prev rule's mpv (= n).
      -- For Cons1 self-recursive, n = mpv = outer's (current single-slot
      -- byte-identical behavior). For Tree slot 0 (NRR external), n = 0
      -- but mpv = 2 — so using n correctly produces NRR-shaped dummies.
      bcd = Dummy.baseCaseDummies { maxProofsVerified: slotN }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      dummyWrapSg = dummySgs.ipa.wrap.sg
      dummyStepSg = dummySgs.ipa.step.sg

      proofsVerifiedMask :: Vector 2 Boolean
      proofsVerifiedMask = (slotN >= 2) :< (slotN >= 1) :< Vector.nil

      stepEndoScalarF :: StepField
      stepEndoScalarF =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    -- All values that vary between BasePrev (b0) and InductivePrev (b1+)
    -- are computed in one case-dispatch block, then handed to a single
    -- buildSlotAdvice call.
    slotData <- case headSlot of
      BasePrev { dummyStatement } -> do
        let
          baseCaseDummyChalPoly =
            { sg: dummyWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }

          msgWrapDigest = hashMessagesForNextWrapProofPureGeneral
            { sg: dummyStepSg
            , paddedChallenges:
                Vector.replicate @2 Dummy.dummyIpaChallenges.wrapExpanded
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
        pure
          { prevStatement: dummyStatement
          , stepOpeningSg: dummyStepSg
          , kimchiPrevSg: dummyStepSg
          , wrapProof: dummyWrapProof bcd
          , wrapPublicInputArr: baseCaseWrapPI
          , prevChalPolys:
              Vector.replicate @2 baseCaseDummyChalPoly
          , wrapPlonkRaw:
              { alpha: bcd.proofDummy.plonk.alpha
              , beta: bcd.proofDummy.plonk.beta
              , gamma: bcd.proofDummy.plonk.gamma
              , zeta: bcd.proofDummy.plonk.zeta
              }
          , wrapPrevEvals: bcd.proofDummy.prevEvals
          , wrapBranchData:
              -- branch_data.domain_log2 of the prev's wrap statement
              -- holds the prev's STEP domain (per OCaml
              -- `Wrap_deferred_values.expand_deferred`'s use of
              -- `Branch_data.domain branch_data` for `step_domain`).
              -- For Tree slot 1 Self at b0 base, this is Tree's own
              -- step domain (= prev = self's step domain).
              { domainLog2: (Curves.fromInt slotParams.slotStepDomainLog2 :: StepField)
              , proofsVerifiedMask
              }
          , wrapSpongeDigest: (zero :: StepField)
          , mustVerify: false
          , wrapOwnPaddedBpChals:
              Vector.replicate @2 Dummy.dummyIpaChallenges.wrapExpanded
          , fopState: fopProofState
          , stepAdvicePrevEvals: bcd.proofDummy.prevEvals
          , kimchiPrevChallengesExpanded: Dummy.dummyIpaChallenges.stepExpanded
          -- BasePrev: prev = dummy wrap, whose deferred.bp_chals =
          -- `Dummy.Ipa.Step.challenges`. All PaddedLength entries are
          -- the dummy step expansion.
          , prevChallengesForStepHash:
              Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
          }
      InductivePrev prevCp prevTag -> do
        let
          CompiledProof prev = prevCp
          Tag { verifier: prevVerifier } = prevTag

          -- Step-field endo expansion of prev's RAW wrap-IPA chals (the
          -- wrap proof's own IPA), for kimchi-level prev_challenges
          -- threading. Not width-dependent; lives outside runExists.
          prevStepBpChalsExpanded :: Vector StepIPARounds StepField
          prevStepBpChalsExpanded =
            map
              ( \sc ->
                  toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                    stepEndoScalarF
              )
              prev.rawBulletproofChallenges

          -- Reconstruct the wrap statement's serialization that
          -- wrapSolveAndProve received as publicInputs.
          wrapPI :: Array WrapField
          wrapPI = wrapPublicInput prevVerifier prevCp

          dummyChalPoly =
            { sg: dummyWrapSg
            , challenges: Dummy.dummyIpaChallenges.wrapExpanded
            }

          paddedLengthInt :: Int
          paddedLengthInt = reflectType (Proxy @PaddedLength)

        -- The width-sized fields (oldBulletproofChallenges,
        -- msgWrapChallenges, outerStepChalPolyComms, wrapDvInput) are
        -- hidden inside prev.widthData :: SomeCompiledProofWidthData.
        -- runExists recovers the typed Vector inside a polymorphic
        -- continuation; we Array-pad to PaddedLength using the
        -- recovered `wd.width :: Int`. The result type doesn't mention
        -- the existential width — only Vector PaddedLength shapes.
        pure $ runExists
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

                runtimeSlotPad :: Int
                runtimeSlotPad = paddedLengthInt - wd.width

                prevRealEntriesArr
                  :: Array
                       { sg :: AffinePoint StepField
                       , challenges :: Vector WrapIPARounds WrapField
                       }
                prevRealEntriesArr = Array.zipWith
                  (\sg ch -> { sg, challenges: ch })
                  (Vector.toUnfoldable wd.outerStepChalPolyComms)
                  (Vector.toUnfoldable wd.msgWrapChallenges)

                prevPaddedChalPolys
                  :: Vector PaddedLength
                       { sg :: AffinePoint StepField
                       , challenges :: Vector WrapIPARounds WrapField
                       }
                prevPaddedChalPolys = unsafePartial $ fromJust
                  $ Vector.toVector @PaddedLength
                  $ Array.replicate runtimeSlotPad dummyChalPoly
                      <> prevRealEntriesArr

                prevPaddedWrapBpChals
                  :: Vector PaddedLength (Vector WrapIPARounds WrapField)
                prevPaddedWrapBpChals = unsafePartial $ fromJust
                  $ Vector.toVector @PaddedLength
                  $
                    Array.replicate runtimeSlotPad
                      Dummy.dummyIpaChallenges.wrapExpanded
                      <> Vector.toUnfoldable wd.msgWrapChallenges

                prevPaddedStepHashChals
                  :: Vector PaddedLength (Vector StepIPARounds StepField)
                prevPaddedStepHashChals = unsafePartial $ fromJust
                  $ Vector.toVector @PaddedLength
                  $
                    Array.replicate runtimeSlotPad
                      Dummy.dummyIpaChallenges.stepExpanded
                      <> Vector.toUnfoldable wd.oldBulletproofChallenges

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
    -- assemble heterogeneously: `Tuple slotSppw restCarrier`,
    -- `Tuple stmt restValCarrier`.
    let
      Tuple _ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
    restResult <- mkStepAdvice @rest restCfg stepCR wrapCR appInput restPrevs

    let
      StepAdvice restA = restResult.stepAdvice
      combinedAdvice = StepAdvice
        { perProofSlotsCarrier: Tuple contrib.slotSppw restA.perProofSlotsCarrier
        , publicInput: appInput
        , publicUnfinalizedProofs:
            contrib.slotUnfinalized :< restA.publicUnfinalizedProofs
        , messagesForNextWrapProof:
            contrib.slotMsgWrapHashStep :< restA.messagesForNextWrapProof
        , messagesForNextWrapProofDummyHash: restA.messagesForNextWrapProofDummyHash
        , wrapVerifierIndex: extractWrapVKCommsAdvice wrapCR.verifierIndex
        , kimchiPrevChallenges:
            contrib.slotKimchiPrevEntry :< restA.kimchiPrevChallenges
        , prevAppStates: Tuple slotData.prevStatement restA.prevAppStates
        }
    pure
      { stepAdvice: combinedAdvice
      , challengePolynomialCommitments:
          contrib.challengePolynomialCommitment :< restResult.challengePolynomialCommitments
      , baseCaseWrapPublicInputs:
          slotData.wrapPublicInputArr :< restResult.baseCaseWrapPublicInputs
      }

  shapeProveData cfg wrapCR sideInfo (Tuple headSlot restPrevs) =
    let
      Tuple headSlotWrapKey restSlotVKs = cfg.perSlotImportedVKs
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

      -- Per-slot data that differs between BasePrev (head = dummy
      -- predecessor) and InductivePrev (head = real prev CompiledProof).
      slotData
        :: { prevSg :: AffinePoint WrapField
           , prevStepChals :: Vector StepIPARounds StepField
           , prevStepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
           , headPrevEvals :: StepAllEvals (F WrapField)
           -- Per-slot prev wrap-IPA bp_chals (Vector n of WrapIPARounds-
           -- sized vectors). For Cons1 self (n=1, prev's mpv=1): single
           -- entry. For Tree slot 0 NRR (n=0, prev mpv=0): empty Vector 0.
           -- For Tree slot 1 self (n=2, prev mpv=2): two entries.
           , headSlotPrevWrapBpChalsVec :: Vector n (Vector WrapIPARounds (F WrapField))
           }
      slotData = case headSlot of
        BasePrev _ ->
          let
            baseCaseDummyChalPoly =
              { sg: wrapSgD, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
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
            pe pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
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
            , prevStepChals: Dummy.dummyIpaChallenges.stepExpanded
            , prevStepAcc: WeierstrassAffinePoint { x: F stepSgD.x, y: F stepSgD.y }
            , headPrevEvals
            , headSlotPrevWrapBpChalsVec:
                Vector.replicate @n (map F Dummy.dummyIpaChallenges.wrapExpanded)
            }
        InductivePrev prevCp prevTag ->
          let
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            -- Step-field endo expansion of prev's RAW wrap-IPA chals
            -- (matches mkStepAdvice's `kimchiPrevChallengesExpanded`).
            -- Not width-dependent; computed outside runExists.
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

            slotNInt :: Int
            slotNInt = reflectType (Proxy @n)
          in
            -- The width-sized fields (oldBulletproofChallenges,
            -- msgWrapChallenges, outerStepChalPolyComms) live inside
            -- prev.widthData :: SomeCompiledProofWidthData. runExists
            -- recovers the typed Vector inside a polymorphic
            -- continuation; we Array-pad both `prevWrapKimchiPrevChals`
            -- (to PaddedLength=2 for the FFI prevChallenges arg) and
            -- `headSlotPrevWrapBpChalsVec` (to the slot's expected `n`)
            -- using `wd.width :: Int`.
            runExists
              ( \(CompiledProofWidthData wd) ->
                  let
                    dummyKimchiArrayEntry =
                      { sgX: wrapSgD.x
                      , sgY: wrapSgD.y
                      , challenges:
                          ( Vector.toUnfoldable Dummy.dummyIpaChallenges.wrapExpanded
                              :: Array WrapField
                          )
                      }
                    prevRealEntries =
                      Vector.toUnfoldable $ Vector.zipWith
                        ( \sg chs ->
                            { sgX: sg.x
                            , sgY: sg.y
                            , challenges:
                                (Vector.toUnfoldable chs :: Array WrapField)
                            }
                        )
                        wd.outerStepChalPolyComms
                        wd.msgWrapChallenges
                    prevPadCount = 2 - wd.width
                    prevWrapKimchiPrevChals =
                      Array.replicate prevPadCount dummyKimchiArrayEntry
                        <> prevRealEntries

                    prevWrapOracles =
                      ProofFFI.vestaProofOracles slotWrapVK
                        { proof: prev.wrapProof
                        , publicInput: prevWrapPI
                        , prevChallenges: prevWrapKimchiPrevChals
                        }

                    peWF pe' = PointEval
                      { zeta: F pe'.zeta
                      , omegaTimesZeta: F pe'.omegaTimesZeta
                      }
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

                    -- Pad prev's `msgWrapChallenges :: Vector wd.width` to
                    -- the slot's expected `Vector n`. For prev width <
                    -- slot n, prepend dummies; for equal, no padding.
                    headSlotPrevWrapBpChalsArr
                      :: Array (Vector WrapIPARounds (F WrapField))
                    headSlotPrevWrapBpChalsArr =
                      Array.replicate (slotNInt - wd.width)
                        (map F Dummy.dummyIpaChallenges.wrapExpanded)
                        <> Vector.toUnfoldable
                          (map (map F) wd.msgWrapChallenges)

                    headSlotPrevWrapBpChalsVec
                      :: Vector n (Vector WrapIPARounds (F WrapField))
                    headSlotPrevWrapBpChalsVec = unsafePartial $ fromJust
                      $ Vector.toVector @n headSlotPrevWrapBpChalsArr
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
      restProveData = shapeProveData @rest restCfg wrapCR restSideInfo restPrevs
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
      -- `allPossibleDomainLog2s = [13, 14, 15]` table at
      -- `Pickles.Prove.Wrap.purs:683`. Earlier code used `slotN`, which
      -- only happens to coincide with the index when there's no
      -- `wrap_domain_override` (Simple_chain). Tree with `override=14`
      -- has `slotN=2` but log2=14 → correct index is 1, not 2. The
      -- old formula caused the wrap circuit's slot 1 FOP to select a
      -- domain whose generator gave a degenerate `inv_` for b1+
      -- (b0 worked because the dummy proof short-circuits past it).
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
-- Polymorphic compile flow
--------------------------------------------------------------------------------

-- | Shape-polymorphic compile flow. Dispatches all shape-specific
-- | data through `CompilableSpec`'s methods (`shapeCompileData`,
-- | `shapeProveData`, `mkStepAdvice`) and uses arithmetic-constraint
-- | resolution to carry `mpv`-derived sizes (outputSize = 33*mpv+1,
-- | etc.) to `stepCompile` / `stepSolveAndProve`.
-- |
-- | All visible type applications on `stepCompile` / `stepSolveAndProve`
-- | / `wrapCompile` / `wrapSolveAndProve` happen in this top-level
-- | function's body where the forall-introduced type variables are
-- | in scope for visible application — not available inside a class
-- | method instance body.
runCompile
  :: forall @prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
       @inputVal inputVar @outputVal outputVar @prevInputVal prevInputVar @m
       pad unfinalizedFieldsTotal digestPlusUnfs outputSize carrierFVar
       totalIpaCommitmentBases totalIpaCommitmentBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfinalizedFieldsTotal
  => Add unfinalizedFieldsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalIpaCommitmentBases
  => Add 1 totalIpaCommitmentBasesPred totalIpaCommitmentBases
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => CheckedType StepField (KimchiConstraint StepField) carrierFVar
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CompileConfig prevsSpec slotVKs
  -> StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> Effect
       ( CompileOutput prevsSpec mpv inputVal outputVal
           (StatementIO inputVal outputVal)
           prevsCarrier
           m
       )
runCompile cfg rule = do
  -- Pre-pass à la OCaml `Fix_domains.domains` (`fix_domains.ml:22-91`):
  -- build the step CS once with placeholder `selfStepDomainLog2 = 20`
  -- (= OCaml `rough_domains.h`) just to count gates and derive the
  -- rule's actual step domain log2. No Rust prover-index creation
  -- happens here, so the cost is just one CS build.
  selfStepDomainLog2 <-
    preComputeStepDomainLog2
      @prevsSpec
      @outputSize
      @valCarrier
      @inputVal
      @inputVar
      @outputVal
      @outputVar
      @prevInputVal
      @prevInputVar
      @mpv
      @0
      -- Single-rule callers always have nd=1 (Self → 1-branch source).
      ( let
          prepDomains :: Vector 1 Int
          prepDomains = 20 :< Vector.nil
        in
          shapeCompileData @prevsSpec cfg prepDomains
      ).stepProveCtx
      rule

  let
    selfDomains :: Vector 1 Int
    selfDomains = selfStepDomainLog2 :< Vector.nil
    shape = shapeCompileData @prevsSpec cfg selfDomains

  stepCR <- stepCompile
    @prevsSpec
    @outputSize
    @valCarrier
    @inputVal
    @inputVar
    @outputVal
    @outputVar
    @prevInputVal
    @prevInputVar
    @mpv
    @0
    shape.stepProveCtx
    rule

  let stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex

  wrapCR <- wrapCompile @1 @slots
    { wrapMainConfig:
        buildWrapMainConfig @mpv cfg.srs.vestaSrs stepCR.verifierIndex
          { domainLog2: stepDomainLog2 }
    , crs: cfg.srs.pallasSrs
    }

  unique <- newUnique

  let
    verifier = mkVerifier
      { wrapVK: wrapCR.verifierIndex
      , vestaSrs: cfg.srs.vestaSrs
      , stepDomainLog2
      }

  pure
    { prover:
        { step: runProverBody
            @prevsSpec
            @slotVKs
            @prevsCarrier
            @mpv
            @slots
            @valCarrier
            @carrier
            @inputVal
            @inputVar
            @outputVal
            @outputVar
            @prevInputVal
            @prevInputVar
            @m
            cfg
            rule
            shape
            stepCR
            wrapCR
            stepDomainLog2
        }
    , tag: Tag { unique, verifier }
    , vks:
        { stepCompileResult: stepCR
        , wrapCompileResult: wrapCR
        , wrapDomainLog2: shape.wrapDomainLog2
        }
    }

-- | Shape-polymorphic prover closure body. Runs the step solver,
-- | computes wrap-side deferred values, runs the wrap solver, and
-- | packages the result. All shape-specific bits come from
-- | `shapeProveData` / `mkStepAdvice` / the pre-computed
-- | `ShapeCompileData`.
runProverBody
  :: forall @prevsSpec @slotVKs @prevsCarrier @mpv @slots @valCarrier @carrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar @m
       pad unfinalizedFieldsTotal digestPlusUnfs outputSize carrierFVar
       totalIpaCommitmentBases totalIpaCommitmentBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier carrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfinalizedFieldsTotal
  => Add unfinalizedFieldsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalIpaCommitmentBases
  => Add 1 totalIpaCommitmentBasesPred totalIpaCommitmentBases
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrier
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrier carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => CheckedType StepField (KimchiConstraint StepField) carrierFVar
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CompileConfig prevsSpec slotVKs
  -> StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> ShapeCompileData mpv 1 slots
  -> StepCompileResult
  -> WrapCompileResult
  -> Int
  -> StepInputs prevsSpec inputVal prevsCarrier
  -> ExceptT ProveError m
       (CompiledProof mpv (StatementIO inputVal outputVal) outputVal Unit)
runProverBody cfg rule shape stepCR wrapCR stepDomainLog2 { appInput, prevs } = do
  { stepAdvice, challengePolynomialCommitments, baseCaseWrapPublicInputs } <- liftEffect $
    mkStepAdvice @prevsSpec cfg stepCR wrapCR appInput prevs

  let
    StepAdvice sa = stepAdvice

    proveDataSideInfo :: ShapeProveSideInfo mpv
    proveDataSideInfo =
      { challengePolynomialCommitments
      , unfinalizedSlots: sa.publicUnfinalizedProofs
      , baseCaseWrapPublicInputs
      }

    proveData = shapeProveData @prevsSpec cfg wrapCR proveDataSideInfo prevs

  stepResult <- stepSolveAndProve
    @prevsSpec
    @outputSize
    @valCarrier
    @inputVal
    @inputVar
    @outputVal
    @outputVar
    @prevInputVal
    @prevInputVar
    @mpv -- mpvMax = mpv (single-rule path)
    @0 -- mpvPad = 0
    shape.stepProveCtx
    rule
    stepCR
    stepAdvice

  let
    -- Assemble the FFI-shaped `prevChallenges` array from the
    -- statically-sized `prevSgs` + `prevStepChallenges` vectors.
    -- `pallasProofOracles` takes `Array { sgX, sgY, challenges :: Array }`
    -- so we convert at the boundary.
    stepOraclesPrevChals = Vector.toUnfoldable $
      Vector.zipWith
        ( \sg chals ->
            { sgX: sg.x, sgY: sg.y, challenges: Vector.toUnfoldable chals }
        )
        proveData.prevSgs
        proveData.prevStepChallenges

    stepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
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
      , zEvals: ProofFFI.proofZEvals stepResult.proof
      , witnessEvals: ProofFFI.proofWitnessEvals stepResult.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals stepResult.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals stepResult.proof
      , indexEvals: ProofFFI.proofIndexEvals stepResult.proof
      }

    wrapDvInput :: WrapDeferredValuesInput mpv
    wrapDvInput =
      { proof: stepResult.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: stepResult.publicInputs
      , allEvals
      -- Singleton because we hardcode `num_chunks = 1` (matches
      -- standard Mina). For circuits exceeding the SRS degree
      -- (`num_chunks > 1`), each commitment splits into multiple
      -- chunks and `pEval0Chunks` becomes a multi-element array.
      -- See `Pickles.VerificationKey:31`, `Pickles.Verify:100-102`,
      -- and `Pickles.Prove.Pure.Wrap:22-24` for the matching TODOs.
      , pEval0Chunks: [ stepOracles.publicEvalZeta ]
      , domainLog2: stepDomainLog2
      , zkRows: 3
      , srsLengthLog2: 16
      , generator: (domainGenerator stepDomainLog2 :: StepField)
      , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
          { domainLog2: stepDomainLog2, zkRows: 3, pt: stepOracles.zeta }
      , omegaForLagrange: \_ -> one
      , endo: let EndoScalar e = endoScalar :: EndoScalar StepField in e
      , linearizationPoly: Linearization.pallas
      , prevSgs: proveData.prevSgs
      , prevChallenges: proveData.prevStepChallenges
      , proofsVerifiedMask: proofsVerifiedMask
      }

    -- Mask is derivable from mpv alone (OCaml common.ml): N=0 → [F,F],
    -- N=1 → [F,T], N=2 → [T,T]. Written in the "slot i real" order.
    outerMpv = reflectType (Proxy @mpv)

    proofsVerifiedMask :: Vector 2 Boolean
    proofsVerifiedMask = (outerMpv >= 2) :< (outerMpv >= 1) :< Vector.nil

    -- Dummy entries used to front-pad msgWrapChallenges and
    -- kimchiPrevEntries from Vector mpv up to Vector PaddedLength=2.
    dummyWrapExpanded :: Vector WrapIPARounds WrapField
    dummyWrapExpanded = Dummy.dummyIpaChallenges.wrapExpanded

    dummyKimchiEntry
      :: { sgX :: StepField, sgY :: StepField, challenges :: Vector WrapIPARounds WrapField }
    dummyKimchiEntry =
      let
        dummyBundle = Dummy.computeDummySgValues
          (Dummy.baseCaseDummies { maxProofsVerified: outerMpv })
          cfg.srs.pallasSrs
          cfg.srs.vestaSrs
        wrapSg = dummyBundle.ipa.wrap.sg
      in
        { sgX: wrapSg.x
        , sgY: wrapSg.y
        , challenges: Dummy.dummyIpaChallenges.wrapExpanded
        }

    msgWrapPadded :: Vector 2 (Vector WrapIPARounds WrapField)
    msgWrapPadded =
      Vector.append (Vector.replicate @pad dummyWrapExpanded) proveData.msgWrapChallenges

    kimchiPrevPadded
      :: Vector 2 { sgX :: StepField, sgY :: StepField, challenges :: Vector WrapIPARounds WrapField }
    kimchiPrevPadded =
      Vector.append (Vector.replicate @pad dummyKimchiEntry) proveData.kimchiPrevEntries

    wrapDv = wrapComputeDeferredValues wrapDvInput

    msgStep :: StepField
    -- Outer-hash digest lives at step PI index `mpv * 32` — the layout
    -- puts the `mpv` unfinalized-proof slots (32 fields each) first,
    -- then the outer hash, then `mpv` width-padding fields. NRR mpv=0
    -- → PI[0]; Simple_chain mpv=1 → PI[32]; Tree mpv=2 → PI[64].
    msgStep = unsafePartial $ fromJust $
      Array.index stepResult.publicInputs (reflectType (Proxy @mpv) * 32)

    stepProofSg :: AffinePoint WrapField
    stepProofSg = ProofFFI.pallasProofOpeningSg stepResult.proof

    msgWrap :: WrapField
    msgWrap = hashMessagesForNextWrapProofPureGeneral
      { sg: stepProofSg
      , paddedChallenges: msgWrapPadded
      }

    wrapCtx =
      { wrapMainConfig:
          buildWrapMainConfig @mpv cfg.srs.vestaSrs stepCR.verifierIndex
            { domainLog2: stepDomainLog2 }
      , crs: cfg.srs.pallasSrs
      , publicInput: assembleWrapMainInput
          { deferredValues: wrapDv
          , messagesForNextStepProofDigest: msgStep
          , messagesForNextWrapProofDigest: msgWrap
          }
      , advice: buildWrapAdvice
          { stepProof: stepResult.proof
          , whichBranch: F zero
          , prevUnfinalizedProofs: proveData.prevUnfinalizedProofs
          , prevMessagesForNextStepProofHash:
              F (fromBigInt (toBigInt msgStep) :: WrapField)
          , prevStepAccs: proveData.prevStepAccs
          , prevOldBpChals: proveData.slotsValue
          , prevEvals: proveData.prevEvals
          , prevWrapDomainIndices: proveData.prevWrapDomainIndices
          }
      , debug: cfg.debug
      , kimchiPrevChallenges: kimchiPrevPadded
      }

  wrapResult <- wrapSolveAndProve @1 @slots wrapCtx wrapCR

  let
    -- The rule's user-defined `publicOutput` value, recovered post-solve
    -- from the FVars `stepMain` captures via Ref. Note: this is NOT
    -- `stepResult.publicOutputs` (which is the kimchi public-output
    -- vector = digest+unfinalized+wrap-msgs); the user's output is
    -- hashed into the outer digest but never appears directly in that
    -- vector. Earlier code mistakenly used `publicOutputs` here, which
    -- corrupted `nrrCp.statement.output` to the digest value and broke
    -- Tree b0 slot 0's IVP via wrong `appStateFields`.
    publicOutput =
      fieldsToValue @StepField stepResult.userPublicOutputFields

  let
    widthData :: SomeCompiledProofWidthData
    widthData = mkSomeCompiledProofWidthData @mpv
      { oldBulletproofChallenges: proveData.prevStepChallenges
      , msgWrapChallenges: proveData.msgWrapChallenges
      , outerStepChalPolyComms:
          map (\e -> { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
      , wrapDvInput
      }

  pure $ CompiledProof
    { statement: StatementIO { input: appInput, output: publicOutput }
    , publicOutput
    , auxiliaryOutput: unit
    , wrapProof: wrapResult.proof
    , rawPlonk: toPlonkMinimal wrapDv.plonk
    , rawBulletproofChallenges: wrapDv.bulletproofPrechallenges
    , branchData: wrapDv.branchData
    , spongeDigestBeforeEvaluations: wrapDv.spongeDigestBeforeEvaluations
    , prevEvals: allEvals
    , pEval0Chunks: [ stepOracles.publicEvalZeta ]
    , challengePolynomialCommitment: stepProofSg
    , messagesForNextStepProofDigest: msgStep
    , messagesForNextWrapProofDigest: msgWrap
    -- Surfaced for `Test.Pickles.Verify.ExpandDeferredEq`: the
    -- prover's `wrapComputeDeferredValues` inputs/output that must
    -- agree with the verifier's `expandDeferredForVerify`
    -- reconstruction at the chain terminus.
    , widthData
    , stepDomainLog2
    , wrapDv
    }
