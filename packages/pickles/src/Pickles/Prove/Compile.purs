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
  , StepInputs
  , Tag(..)
  , class CompilableSpec
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
import Data.Functor.Product (Product, product)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Type.Proxy (Proxy(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy as Dummy
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
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
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap
  ( WrapDeferredValuesInput
  , assembleWrapMainInput
  , wrapComputeDeferredValues
  )
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.Prove.Step
  ( StepAdvice(..)
  , StepCompileResult
  , StepProveContext
  , StepRule
  , buildStepAdvice
  , buildStepAdviceWithOracles
  , dummyWrapTockPublicInput
  , extractWrapVKCommsAdvice
  , stepCompile
  , stepSolveAndProve
  )
import Snarky.Circuit.DSL.SizedF (unwrapF, wrapF) as SizedF
import Snarky.Curves.Class (fromInt) as Curves
import Pickles.Prove.Wrap
  ( WrapCompileResult
  , buildWrapAdvice
  , buildWrapMainConfig
  , wrapCompile
  , wrapSolveAndProve
  )
import Pickles.Prove.Verify
  ( CompiledProof(..)
  , Verifier
  , mkVerifier
  , verify
  , verifyOne
  , wrapPublicInput
  )
import Pickles.Step.Prevs (class PrevValuesCarrier, class PrevsCarrier, PrevsSpecCons, PrevsSpecNil)
import Pickles.Util.Unique (Unique, newUnique)
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
import Pickles.Verify.Types (toPlonkMinimal)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (class PadSlots, NoSlots, noSlots)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), coerceViaBits)
import Snarky.Circuit.Kimchi (fromShifted, toShifted) as Kimchi
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.Types (class CircuitType, BoolVar, fieldsToValue)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (SplitField, Type2)

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
  { step :: StepInputs prevsSpec inputVal prevsCarrier
         -> ExceptT ProveError m (CompiledProof mpv stmtVal outputVal Unit)
  }

type CompileConfig :: Type -> Type -> Type
type CompileConfig prevsSpec slotVKs =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , perSlotImportedVKs :: slotVKs
  , debug :: Boolean
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
-- | * `stepWidth` — `buildWrapMainConfig`'s `stepWidth` argument
-- |   (= mpv).
-- | * `slotsValue` — runtime realisation of the `slots` type
-- |   constructor (`noSlots`, `slots1 ...`, etc.) carrying each prev's
-- |   wrap bp-challenges.
type ShapeCompileData :: Int -> (Type -> Type) -> Type
type ShapeCompileData mpv slots =
  { stepProveCtx :: StepProveContext mpv
  , wrapDomainLog2 :: Int
  , stepWidth :: Int
  }

-- | Side info from `mkStepAdvice`'s return that `shapeProveData` needs.
-- |
-- | * `b0ChalPolyComm` — outer rule's step-proof opening sg; feeds the
-- |   kimchi-prev real entry.
-- | * `unfinalizedSlots` — per-slot step-field unfinalized proofs,
-- |   Type1→Type2 coerced in `shapeProveData` to build
-- |   `prevUnfinalizedProofs`.
-- | * `baseCaseWrapPublicInput` — serialized `dummyWrapTockPublicInput`
-- |   array, passed to `vestaProofOracles` so `shapeProveData`'s
-- |   `dummyWrapXhat` evals match what the step circuit sees.
-- |
-- | For recursion: each Cons level calls `shapeProveData @rest` with
-- | `unfinalizedSlots` trimmed via `Vector.tail` to drop the head slot.
type ShapeProveSideInfo :: Int -> Type
type ShapeProveSideInfo mpv =
  { b0ChalPolyComm :: AffinePoint StepField
  , unfinalizedSlots ::
      Vector mpv
        ( PerProofUnfinalized WrapIPARounds
            (Type2 (SplitField (F StepField) Boolean))
            (F StepField)
            Boolean
        )
  , baseCaseWrapPublicInput :: Array WrapField
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
  { -- | Per-slot entries for `pallasProofOracles.prevChallenges`. The
    -- | FFI takes an Array (not a Vector) so we use Array here; order
    -- | is slot 0 first.
    stepOraclesPrevChallenges ::
      Array
        { sgX :: WrapField
        , sgY :: WrapField
        , challenges :: Array StepField
        }
  , prevSgs :: Vector mpv (AffinePoint WrapField)
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
  :: Type -> Type -> Type -> Int -> (Type -> Type) -> Type -> Constraint
class
  CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier
  | prevsSpec -> slotVKs prevsCarrier mpv slots valCarrier
  where
  -- | Compile-time shape data (stepProveCtx, constants). Nil: empty
  -- | per-slot vectors + wrapDomainLog2=13 + stepWidth=0 + noSlots.
  -- | Cons: populated from `perSlotImportedVKs` + `wrapDomainLog2`
  -- | for its mpv.
  shapeCompileData
    :: CompileConfig prevsSpec slotVKs
    -> ShapeCompileData mpv slots

  -- | Step solver advice + side info. Non-recursive: called once per
  -- | `prover.step` invocation, at the outer rule level (never delegates
  -- | to `rest`). Nil uses `buildStepAdvice`; Cons uses
  -- | `buildStepAdviceWithOracles` (returning the step proof's
  -- | `challengePolynomialCommitment`).
  -- |
  -- | `sideInfo` packages the outputs needed by `shapeProveData` that
  -- | can only be known after the step advice is built:
  -- |
  -- | * `challengePolynomialCommitment` — used by
  -- |   `kimchiPrevEntries`'s real-slot entry.
  -- | * `publicUnfinalizedProofs` — per-slot step-field unfinalized
  -- |   proofs, Type1→Type2 coerced into wrap-field for
  -- |   `prevUnfinalizedProofs`.
  mkStepAdvice
    :: forall inputVal inputVar carrier
     . CircuitType StepField inputVal inputVar
    => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
         (F StepField)
         (Type2 (SplitField (F StepField) Boolean))
         Boolean
         mpv
         carrier
    => CompileConfig prevsSpec slotVKs
    -> StepCompileResult
    -> WrapCompileResult
    -> inputVal
    -> prevsCarrier
    -> Int
    -> Effect
         { stepAdvice ::
             StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal mpv
               carrier
               valCarrier
         , challengePolynomialCommitment :: AffinePoint StepField
         , baseCaseWrapPublicInput :: Array WrapField
         }

  -- | Per-slot wrap-stage data. Recursive: cons head slot's entries
  -- | onto `shapeProveData @rest` output. Takes the outer rule's
  -- | step-advice side info (`b0ChalPolyComm`, publicUnfinalizedProofs)
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
  :: forall @prevsSpec slotVKs prevsCarrier mpv slots valCarrier
       @inputVal inputVar @outputVal outputVar @prevInputVal prevInputVar @m
       pad unfsTotal digestPlusUnfs outputSize carrierF carrierFVar
       branchesPred totalBases totalBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalBases
  => Add 1 totalBasesPred totalBases
  => Add 1 branchesPred 1
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrierF
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrierF carrierFVar
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
       (CompileOutput prevsSpec mpv inputVal outputVal
          (StatementIO inputVal outputVal) prevsCarrier m)
compile cfg rule = runCompile
  @prevsSpec @inputVal @outputVal @prevInputVal @m
  cfg rule

--------------------------------------------------------------------------------
-- CompilableSpec PrevsSpecNil (N=0, NRR-shape)
--------------------------------------------------------------------------------

-- | Ro-derived `Dummy.Ipa.Wrap.sg`. Unused at N=0 (no `verify_one`) but
-- | required by `stepCompile` as the sg_old padding constant.
nrrDummyWrapSg :: CRS PallasG -> CRS VestaG -> AffinePoint StepField
nrrDummyWrapSg pallasSrs vestaSrs =
  (Dummy.computeDummySgValues
     (Dummy.baseCaseDummies { maxProofsVerified: 0 })
     pallasSrs
     vestaSrs).ipa.wrap.sg

instance CompilableSpec PrevsSpecNil Unit Unit 0 NoSlots Unit where
  shapeCompileData cfg =
    { stepProveCtx:
        { srsData:
            { perSlotLagrangeAt: Vector.nil
            , blindingH:
                (coerce $ ProofFFI.vestaSrsBlindingGenerator cfg.srs.pallasSrs)
                  :: AffinePoint (F StepField)
            , perSlotFopDomainLog2: Vector.nil
            , perSlotKnownWrapKeys: Vector.nil
            }
        , dummySg: nrrDummyWrapSg cfg.srs.pallasSrs cfg.srs.vestaSrs
        , crs: cfg.srs.vestaSrs
        , debug: cfg.debug
        }
    , wrapDomainLog2: 13
    , stepWidth: 0
    }

  mkStepAdvice cfg _stepCR wrapCR appInput _prevs wrapDomainLog2 =
    let
      StepAdvice base = buildStepAdvice @PrevsSpecNil
        { publicInput: appInput, wrapDomainLog2, prevAppStates: unit }
      stepAdvice = StepAdvice
        (base { wrapVerifierIndex = extractWrapVKCommsAdvice wrapCR.verifierIndex })
      -- Nil has no prev slots, so these sideInfo fields are never
      -- consumed by shapeProveData (which returns empty vectors).
      challengePolynomialCommitment = nrrDummyWrapSg cfg.srs.pallasSrs cfg.srs.vestaSrs
    in
      pure
        { stepAdvice
        , challengePolynomialCommitment
        , baseCaseWrapPublicInput: []
        }

  shapeProveData _cfg _wrapCR _sideInfo _prevs =
    { stepOraclesPrevChallenges: []
    , prevSgs: Vector.nil
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
  ( CompilableSpec rest Unit restPrevsCarrier restMpv restSlots Unit
  , Add restMpv 1 mpv
  , Add 1 restMpv mpv
  , Add pad mpv PaddedLength
  , Reflectable n Int
  , Reflectable mpv Int
  , Reflectable pad Int
  , Compare mpv 3 LT
  , Compare 0 mpv LT
  , Compare 0 n LT
  , CircuitType StepField prevHeadInput prevHeadInputVar
  , CircuitType StepField prevHeadOutput prevHeadOutputVar
  , PrevValuesCarrier rest Unit
  ) =>
  CompilableSpec
    (PrevsSpecCons n (StatementIO prevHeadInput prevHeadOutput) rest)
    (Tuple SlotWrapKey Unit)
    ( Tuple
        (PrevSlot prevHeadInput n (StatementIO prevHeadInput prevHeadOutput) prevHeadOutput)
        restPrevsCarrier
    )
    mpv
    (Product (Vector n) restSlots)
    (Tuple (StatementIO prevHeadInput prevHeadOutput) Unit)
  where
  shapeCompileData cfg =
    let
      Tuple headSlotWrapKey restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      restShape = shapeCompileData @rest restCfg
      outerMpv = reflectType (Proxy @mpv)
      outerWrapDomainLog2 = Dummy.wrapDomainLog2ForProofsVerified outerMpv

      slotN = reflectType (Proxy @n)
      slotWrapDomainLog2 = Dummy.wrapDomainLog2ForProofsVerified slotN

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
              , perSlotFopDomainLog2:
                  slotWrapDomainLog2 :< restShape.stepProveCtx.srsData.perSlotFopDomainLog2
              , perSlotKnownWrapKeys:
                  headKnownWrapKey :< restShape.stepProveCtx.srsData.perSlotKnownWrapKeys
              }
          , dummySg: outerDummySgs.ipa.wrap.sg
          , crs: cfg.srs.vestaSrs
          , debug: cfg.debug
          }
      , wrapDomainLog2: outerWrapDomainLog2
      , stepWidth: outerMpv
      }

  mkStepAdvice cfg _stepCR wrapCR appInput (Tuple headSlot _restPrevs) wrapDomainLog2 = do
    let
      outerMpv = reflectType (Proxy @mpv)
      bcd = Dummy.baseCaseDummies { maxProofsVerified: outerMpv }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      dummyWrapSg = dummySgs.ipa.wrap.sg
      dummyStepSg = dummySgs.ipa.step.sg

      proofsVerifiedMask :: Vector 2 Boolean
      proofsVerifiedMask = (outerMpv >= 2) :< (outerMpv >= 1) :< Vector.nil

      stepEndoScalarF :: StepField
      stepEndoScalarF =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    -- All values that vary between BasePrev (b0) and InductivePrev (b1+)
    -- are computed in one case-dispatch block, then handed to a single
    -- buildStepAdviceWithOracles call.
    slotData <- case headSlot of
      BasePrev { dummyStatement } -> do
        let
          baseCaseDummyChalPoly =
            { sg: dummyWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }

          msgWrapDigest = hashMessagesForNextWrapProofPureGeneral
            { sg: dummyStepSg
            , paddedChallenges:
                Dummy.dummyIpaChallenges.wrapExpanded
                  :< Dummy.dummyIpaChallenges.wrapExpanded
                  :< Vector.nil
            }

          fopProofState = Dummy.stepDummyUnfinalizedProof @mpv bcd
            { domainLog2: Dummy.wrapDomainLog2ForProofsVerified outerMpv }
            (map SizedF.wrapF bcd.ipaStepChallenges)

          baseCaseWrapPI = dummyWrapTockPublicInput @mpv
            { wrapDomainLog2
            , wrapVK: wrapCR.verifierIndex
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
              baseCaseDummyChalPoly :< baseCaseDummyChalPoly :< Vector.nil
          , wrapPlonkRaw:
              { alpha: bcd.proofDummy.plonk.alpha
              , beta: bcd.proofDummy.plonk.beta
              , gamma: bcd.proofDummy.plonk.gamma
              , zeta: bcd.proofDummy.plonk.zeta
              }
          , wrapPrevEvals: bcd.proofDummy.prevEvals
          , wrapBranchData:
              { domainLog2: (Curves.fromInt wrapDomainLog2 :: StepField)
              , proofsVerifiedMask
              }
          , wrapSpongeDigest: (zero :: StepField)
          , mustVerify: false
          , wrapOwnPaddedBpChals:
              Dummy.dummyIpaChallenges.wrapExpanded
                :< Dummy.dummyIpaChallenges.wrapExpanded
                :< Vector.nil
          , fopState: fopProofState
          , stepAdvicePrevEvals: bcd.proofDummy.prevEvals
          , kimchiPrevChallengesExpanded: Dummy.dummyIpaChallenges.stepExpanded
          -- BasePrev: prev = dummy wrap, whose deferred.bp_chals =
          -- `Dummy.Ipa.Step.challenges`. The hashed bp-chals vector
          -- (= step_b's `messages_for_next_step_proof.old_bp_chals`
          -- per slot) is the dummy expansion. Replicate to the
          -- per-slot Vector.
          , prevChalsForStepHashHead: Dummy.dummyIpaChallenges.stepExpanded
          }
      InductivePrev prevCp prevTag -> do
        let
          CompiledProof prev = prevCp
          Tag { verifier: prevVerifier } = prevTag

          -- Reconstruct prev's full WrapDeferredValuesOutput via the
          -- verifier-side helper. ExpandDeferredEq proves this matches
          -- what `wrapComputeDeferredValues` originally produced —
          -- byte-exact source for `fopState` fields not directly
          -- stored on CompiledProof (combinedInnerProduct, xi, b,
          -- full plonk).
          prevZetaField :: StepField
          prevZetaField =
            coerce (toFieldPure prev.rawPlonk.zeta (F prevVerifier.stepEndo))

          prevVanishesOnZk :: StepField
          prevVanishesOnZk = ProofFFI.permutationVanishingPolynomial
            { domainLog2: prevVerifier.stepDomainLog2
            , zkRows: prevVerifier.stepZkRows
            , pt: prevZetaField
            }

          prevDv = expandDeferredForVerify
            { rawPlonk: prev.rawPlonk
            , rawBulletproofChallenges: prev.rawBulletproofChallenges
            , branchData: prev.branchData
            , spongeDigestBeforeEvaluations: prev.spongeDigestBeforeEvaluations
            , allEvals: prev.prevEvals
            , pEval0Chunks: prev.pEval0Chunks
            , oldBulletproofChallenges: prev.oldBulletproofChallenges
            , domainLog2: prevVerifier.stepDomainLog2
            , zkRows: prevVerifier.stepZkRows
            , srsLengthLog2: prevVerifier.stepSrsLengthLog2
            , generator: prevVerifier.stepGenerator
            , shifts: prevVerifier.stepShifts
            , vanishesOnZk: prevVanishesOnZk
            , omegaForLagrange: \_ -> one
            , endo: prevVerifier.stepEndo
            , linearizationPoly: prevVerifier.linearizationPoly
            }

          -- prev wrap-side bp chals (the chals that prev hashed into
          -- its `messages_for_next_wrap_proof_digest`), retrieved from
          -- prev's stored `msgWrapChallenges` (head slot). For
          -- Simple_chain b1 where prev = b0 (base case), these are
          -- dummy chals; for deeper inductions they're real.
          prevWrapMsgChals :: Vector WrapIPARounds WrapField
          prevWrapMsgChals = Vector.head prev.msgWrapChallenges

          -- Step-field endo expansion of prev's RAW wrap-IPA chals (the
          -- wrap proof's own IPA), for kimchi-level prev_challenges
          -- threading.
          prevStepBpChalsExpanded :: Vector StepIPARounds StepField
          prevStepBpChalsExpanded =
            map
              ( \sc ->
                  toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                    stepEndoScalarF
              )
              prev.rawBulletproofChallenges

          dummyChalPoly =
            { sg: dummyWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }

          -- The sg that prev's `expand_proof` returned at the time it
          -- generated its own wrap proof — i.e. prev's outer step
          -- proof's `expandProof.challenge_polynomial_commitment`
          -- (= `vestaProofOpeningSg prev_prev.wrapProof` for prev's
          -- inductive case, OR `compute_sg` for prev's base case).
          -- Stored on prev's CompiledProof at compile time via
          -- `runCompile`'s `outerStepChalPolyComms`. Fed into b1's
          -- `prevChalPolys[real].sg` which serves DOUBLE DUTY: source
          -- for both the in-circuit `messages_for_next_step_proof.cpc`
          -- hash AND the `wrapOraclesPrevChallenges` sgX/sgY (= what
          -- prev.wrapProof was generated with, so kimchi's oracle
          -- replay matches).
          realChalPolySg :: AffinePoint StepField
          realChalPolySg = Vector.head prev.outerStepChalPolyComms

          realChalPoly =
            { sg: realChalPolySg
            , challenges: prevWrapMsgChals
            }

          fopState =
            { deferredValues:
                { plonk: prevDv.plonk
                , combinedInnerProduct: prevDv.combinedInnerProduct
                , xi: prevDv.xi
                , bulletproofChallenges: prevDv.bulletproofPrechallenges
                , b: prevDv.b
                }
            , shouldFinalize: false
            , spongeDigestBeforeEvaluations: F prevDv.spongeDigestBeforeEvaluations
            }

          -- Reconstruct the wrap statement's serialization that
          -- wrapSolveAndProve received as publicInputs. Verified
          -- byte-exact in CompileSmoke's NRR byte-identity test.
          wrapPI :: Array WrapField
          wrapPI = wrapPublicInput prevVerifier prevCp
        pure
          { prevStatement: prev.statement
          , stepOpeningSg: prev.challengePolynomialCommitment
          , kimchiPrevSg: prev.challengePolynomialCommitment
          , wrapProof: prev.wrapProof
          , wrapPublicInputArr: wrapPI
          -- For mpv=1: front-padded `[dummy, real]` (Wrap_hack pad). For
          -- mpv=2: would be `[real_slot0, real_slot1]` — Tree case
          -- needs separate handling.
          , prevChalPolys: dummyChalPoly :< realChalPoly :< Vector.nil
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
          -- mpv=1: `[dummy, real]`. mpv=2 Tree: `[real_slot0, real_slot1]`.
          , wrapOwnPaddedBpChals:
              Dummy.dummyIpaChallenges.wrapExpanded
                :< prevWrapMsgChals
                :< Vector.nil
          , fopState
          , stepAdvicePrevEvals: prev.prevEvals
          , kimchiPrevChallengesExpanded: prevStepBpChalsExpanded
          -- InductivePrev: the value step_b_k's
          -- `messages_for_next_step_proof.old_bp_chals` hash absorbs is
          -- `wrap_b_{k-2}.deferred.bp_chals` step-expanded — already
          -- stored on prev's CompiledProof as
          -- `oldBulletproofChallenges` (set during prev's runCompile
          -- via shapeProveData's `prevStepChals`). Vector.head extracts
          -- the head slot for self-recursive mpv=1 rules.
          , prevChalsForStepHashHead: Vector.head prev.oldBulletproofChallenges
          }

    { advice, challengePolynomialCommitment } <- buildStepAdviceWithOracles
      @mpv
      @(PrevsSpecCons n (StatementIO prevHeadInput prevHeadOutput) rest)
      { publicInput: appInput
      , prevStatement: slotData.prevStatement
      , wrapDomainLog2
      , stepDomainLog2: wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
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
      , prevChallengesForStepHash:
          Vector.replicate slotData.prevChalsForStepHashHead
      }
    pure
      { stepAdvice: advice
      , challengePolynomialCommitment
      , baseCaseWrapPublicInput: slotData.wrapPublicInputArr
      }

  shapeProveData cfg wrapCR sideInfo (Tuple headSlot restPrevs) =
    let
      Tuple _ restSlotVKs = cfg.perSlotImportedVKs
      restCfg = cfg { perSlotImportedVKs = restSlotVKs }
      outerMpv = reflectType (Proxy @mpv)
      slotN = reflectType (Proxy @n)
      bcd = Dummy.baseCaseDummies { maxProofsVerified: outerMpv }
      dummySgs = Dummy.computeDummySgValues bcd cfg.srs.pallasSrs cfg.srs.vestaSrs
      wrapSgD = dummySgs.ipa.wrap.sg   -- AffinePoint StepField
      stepSgD = dummySgs.ipa.step.sg   -- AffinePoint WrapField

      PerProofUnfinalized headUnfRaw = Vector.head sideInfo.unfinalizedSlots
      tailUnfinalized = Vector.tail sideInfo.unfinalizedSlots

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
            F (fromBigInt (toBigInt (case headUnfRaw.spongeDigest of F x -> x)) :: WrapField)
        , beta: UnChecked (coerceViaBits (case headUnfRaw.beta of UnChecked v -> v))
        , gamma: UnChecked (coerceViaBits (case headUnfRaw.gamma of UnChecked v -> v))
        , alpha: UnChecked (coerceViaBits (case headUnfRaw.alpha of UnChecked v -> v))
        , zeta: UnChecked (coerceViaBits (case headUnfRaw.zeta of UnChecked v -> v))
        , xi: UnChecked (coerceViaBits (case headUnfRaw.xi of UnChecked v -> v))
        , bulletproofChallenges:
            map (\(UnChecked v) -> UnChecked (coerceViaBits v))
              headUnfRaw.bulletproofChallenges
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
      slotData ::
        { stepOraclesPrevChalEntry ::
            { sgX :: WrapField, sgY :: WrapField, challenges :: Array StepField }
        , prevSg :: AffinePoint WrapField
        , prevStepChals :: Vector StepIPARounds StepField
        , prevStepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
        , headPrevEvals :: StepAllEvals (F WrapField)
        , headSlotWrapBpChals :: Vector WrapIPARounds (F WrapField)
        }
      slotData = case headSlot of
        BasePrev _ ->
          let
            baseCaseDummyChalPoly =
              { sg: wrapSgD, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
            toFFI r =
              { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
            dummyWrapOracles =
              ProofFFI.vestaProofOracles wrapCR.verifierIndex
                { proof: dummyWrapProof bcd
                , publicInput: sideInfo.baseCaseWrapPublicInput
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
            { stepOraclesPrevChalEntry:
                { sgX: stepSgD.x
                , sgY: stepSgD.y
                , challenges: Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
                }
            , prevSg: stepSgD
            , prevStepChals: Dummy.dummyIpaChallenges.stepExpanded
            , prevStepAcc: WeierstrassAffinePoint { x: F stepSgD.x, y: F stepSgD.y }
            , headPrevEvals
            , headSlotWrapBpChals: map F Dummy.dummyIpaChallenges.wrapExpanded
            }
        InductivePrev prevCp prevTag ->
          let
            CompiledProof prev = prevCp
            Tag { verifier: prevVerifier } = prevTag

            -- Step-field endo expansion of prev's RAW wrap-IPA chals
            -- (matches mkStepAdvice's `kimchiPrevChallengesExpanded`).
            prevStepBpChalsExpanded :: Vector StepIPARounds StepField
            prevStepBpChalsExpanded =
              map
                ( \sc ->
                    toFieldPure (coerceViaBits sc :: SizedF 128 StepField)
                      stepEndoScalarF
                )
                prev.rawBulletproofChallenges

            -- Reproduce the kimchi prev_challenges that were used to
            -- generate prev.wrapProof. Each of prev's `n` slots
            -- contributes a real entry; front-pad with dummies to
            -- reach PaddedLength=2 (matches `runCompile`'s padding).
            dummyKimchiArrayEntry =
              { sgX: wrapSgD.x
              , sgY: wrapSgD.y
              , challenges:
                  (Vector.toUnfoldable Dummy.dummyIpaChallenges.wrapExpanded :: Array WrapField)
              }
            prevRealEntries =
              Vector.toUnfoldable $ Vector.zipWith
                ( \sg chs ->
                    { sgX: sg.x
                    , sgY: sg.y
                    , challenges: (Vector.toUnfoldable chs :: Array WrapField)
                    }
                )
                prev.outerStepChalPolyComms
                prev.msgWrapChallenges
            prevPadCount = 2 - reflectType (Proxy @n)
            prevWrapKimchiPrevChals =
              Array.replicate prevPadCount dummyKimchiArrayEntry <> prevRealEntries

            prevWrapPI :: Array WrapField
            prevWrapPI = wrapPublicInput prevVerifier prevCp

            prevWrapOracles =
              ProofFFI.vestaProofOracles wrapCR.verifierIndex
                { proof: prev.wrapProof
                , publicInput: prevWrapPI
                , prevChallenges: prevWrapKimchiPrevChals
                }

            peWF pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
            prevHeadPrevEvals = StepAllEvals
              { ftEval1: F prevWrapOracles.ftEval1
              , publicEvals: PointEval
                  { zeta: F prevWrapOracles.publicEvalZeta
                  , omegaTimesZeta: F prevWrapOracles.publicEvalZetaOmega
                  }
              , zEvals: peWF (ProofFFI.proofZEvals prev.wrapProof)
              , witnessEvals: map peWF (ProofFFI.proofWitnessEvals prev.wrapProof)
              , coeffEvals: map peWF (ProofFFI.proofCoefficientEvals prev.wrapProof)
              , sigmaEvals: map peWF (ProofFFI.proofSigmaEvals prev.wrapProof)
              , indexEvals: map peWF (ProofFFI.proofIndexEvals prev.wrapProof)
              }
          in
            { stepOraclesPrevChalEntry:
                { sgX: prev.challengePolynomialCommitment.x
                , sgY: prev.challengePolynomialCommitment.y
                , challenges: Vector.toUnfoldable prevStepBpChalsExpanded
                }
            , prevSg: prev.challengePolynomialCommitment
            , prevStepChals: prevStepBpChalsExpanded
            , prevStepAcc: WeierstrassAffinePoint
                { x: F prev.challengePolynomialCommitment.x
                , y: F prev.challengePolynomialCommitment.y
                }
            , headPrevEvals: prevHeadPrevEvals
            -- Prev's first slot's bp-chals (= what prev hashed into
            -- `messages_for_next_wrap_proof` at slot 0, the chals THIS
            -- rule's wrap circuit verifies when consuming prev's
            -- wrap proof).
            , headSlotWrapBpChals: map F (Vector.head prev.msgWrapChallenges)
            }

      -- Recurse into rest.
      restSideInfo :: ShapeProveSideInfo restMpv
      restSideInfo =
        { b0ChalPolyComm: sideInfo.b0ChalPolyComm
        , unfinalizedSlots: tailUnfinalized
        , baseCaseWrapPublicInput: sideInfo.baseCaseWrapPublicInput
        }
      restProveData = shapeProveData @rest restCfg wrapCR restSideInfo restPrevs
    in
      { stepOraclesPrevChallenges:
          [ slotData.stepOraclesPrevChalEntry ] <> restProveData.stepOraclesPrevChallenges
      , prevSgs: slotData.prevSg :< restProveData.prevSgs
      , prevStepChallenges:
          slotData.prevStepChals :< restProveData.prevStepChallenges
      , msgWrapChallenges:
          msgForNextWrapRealChals :< restProveData.msgWrapChallenges
      , prevUnfinalizedProofs: headUnfinalizedWrap :< restProveData.prevUnfinalizedProofs
      , prevStepAccs: slotData.prevStepAcc :< restProveData.prevStepAccs
      , prevEvals: slotData.headPrevEvals :< restProveData.prevEvals
      , prevWrapDomainIndices:
          F (Curves.fromInt slotN :: WrapField) :< restProveData.prevWrapDomainIndices
      , kimchiPrevEntries:
          { sgX: sideInfo.b0ChalPolyComm.x
          , sgY: sideInfo.b0ChalPolyComm.y
          , challenges: msgForNextWrapRealChals
          } :< restProveData.kimchiPrevEntries
      , slotsValue:
          product (Vector.replicate @n slotData.headSlotWrapBpChals) restProveData.slotsValue
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
  :: forall @prevsSpec slotVKs prevsCarrier mpv slots valCarrier
       @inputVal inputVar @outputVal outputVar @prevInputVal prevInputVar @m
       pad unfsTotal digestPlusUnfs outputSize carrierF carrierFVar
       branchesPred totalBases totalBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalBases
  => Add 1 totalBasesPred totalBases
  => Add 1 branchesPred 1
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrierF
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrierF carrierFVar
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
       (CompileOutput prevsSpec mpv inputVal outputVal
          (StatementIO inputVal outputVal) prevsCarrier m)
runCompile cfg rule = do
  let
    shape = shapeCompileData @prevsSpec cfg

  stepCR <- stepCompile
    @prevsSpec @outputSize @valCarrier
    @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
    shape.stepProveCtx rule

  let stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex

  wrapCR <- wrapCompile @1 @slots
    { wrapMainConfig:
        buildWrapMainConfig cfg.srs.vestaSrs stepCR.verifierIndex
          { stepWidth: shape.stepWidth, domainLog2: stepDomainLog2 }
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
            @prevsSpec @slotVKs @prevsCarrier @mpv @slots @valCarrier
            @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
            @m
            cfg rule shape stepCR wrapCR stepDomainLog2
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
  :: forall @prevsSpec @slotVKs @prevsCarrier @mpv @slots @valCarrier
       @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar @m
       pad unfsTotal digestPlusUnfs outputSize carrierF carrierFVar
       branchesPred totalBases totalBasesPred
   . CompilableSpec prevsSpec slotVKs prevsCarrier mpv slots valCarrier
  => PrevValuesCarrier prevsSpec valCarrier
  => MonadEffect m
  => CircuitGateConstructor StepField VestaG
  => CircuitGateConstructor WrapField PallasG
  => Reflectable mpv Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad mpv PaddedLength
  => Mul mpv 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpv outputSize
  => Compare mpv 3 LT
  => Add mpv 45 totalBases
  => Add 1 totalBasesPred totalBases
  => Add 1 branchesPred 1
  => PadSlots slots mpv
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       mpv
       carrierF
  => PrevsCarrier prevsSpec StepIPARounds WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       mpv
       carrierFVar
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CircuitType StepField prevInputVal prevInputVar
  => CircuitType StepField carrierF carrierFVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => CheckedType StepField (KimchiConstraint StepField) carrierFVar
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CompileConfig prevsSpec slotVKs
  -> StepRule mpv valCarrier inputVal inputVar outputVal outputVar prevInputVal prevInputVar
  -> ShapeCompileData mpv slots
  -> StepCompileResult
  -> WrapCompileResult
  -> Int
  -> StepInputs prevsSpec inputVal prevsCarrier
  -> ExceptT ProveError m
       (CompiledProof mpv (StatementIO inputVal outputVal) outputVal Unit)
runProverBody cfg rule shape stepCR wrapCR stepDomainLog2 { appInput, prevs } = do
  { stepAdvice, challengePolynomialCommitment, baseCaseWrapPublicInput } <- liftEffect $
    mkStepAdvice @prevsSpec cfg stepCR wrapCR appInput prevs shape.wrapDomainLog2

  let
    StepAdvice sa = stepAdvice
    proveDataSideInfo :: ShapeProveSideInfo mpv
    proveDataSideInfo =
      { b0ChalPolyComm: challengePolynomialCommitment
      , unfinalizedSlots: sa.publicUnfinalizedProofs
      , baseCaseWrapPublicInput
      }

    proveData = shapeProveData @prevsSpec cfg wrapCR proveDataSideInfo prevs

  stepResult <- stepSolveAndProve
    @prevsSpec @outputSize @valCarrier
    @inputVal @inputVar @outputVal @outputVar @prevInputVal @prevInputVar
    shape.stepProveCtx rule stepCR stepAdvice

  let
    stepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
      { proof: stepResult.proof
      , publicInput: stepResult.publicInputs
      , prevChallenges: proveData.stepOraclesPrevChallenges
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
          buildWrapMainConfig cfg.srs.vestaSrs stepCR.verifierIndex
            { stepWidth: shape.stepWidth, domainLog2: stepDomainLog2 }
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
    publicOutput = fieldsToValue @StepField
      (map (\(F x) -> x) (Vector.toUnfoldable stepResult.publicOutputs))

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
    , oldBulletproofChallenges: proveData.prevStepChallenges
    , challengePolynomialCommitment: stepProofSg
    , messagesForNextStepProofDigest: msgStep
    , messagesForNextWrapProofDigest: msgWrap
    , msgWrapChallenges: proveData.msgWrapChallenges
    , outerStepChalPolyComms: map (\e -> { x: e.sgX, y: e.sgY }) proveData.kimchiPrevEntries
    }
