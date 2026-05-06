module Pickles.CircuitDiffs.PureScript.Common
  ( CompiledCircuit
  , StepArtifact
  , WrapArtifact
  , mkStepArtifact
  , domainLog2OfCompiled
  , preComputeSelfStepDomainLog2
  , unsafeIdx
  , asSizedF128
  , asSizedF10
  , dummyVestaPt
  , dummyPallasPt
  , dummyWrapSg
  , domainLog2
  , stepEndo
  , wrapEndo
  , srsLengthLog2
  , wrapDomainLog2
  , wrapSrsLengthLog2
  , deriveStepVKFromCompiled
  , deriveWrapVKFromCompiled
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Prove.Step (extractWrapVKCommsAdvice)
import Pickles.Prove.Wrap (extractStepVKComms, stepVkForCircuit)
import Pickles.Types (StepField, VerificationKey, WrapField)
import Pickles.VerificationKey (StepVK)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges)
import Snarky.Backend.Kimchi.Class (createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar, SizedF)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), EndoScalar(..), endoBase, endoScalar, fromBigInt, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- | Compiled circuit type
-------------------------------------------------------------------------------

type CompiledCircuit f = CircuitBuilderState (KimchiGate f) (AuxState f)

-------------------------------------------------------------------------------
-- | Input parsing helpers
-------------------------------------------------------------------------------

unsafeIdx :: forall n f. Vector n f -> Int -> f
unsafeIdx v i =
  let
    arr = Vector.toUnfoldable v :: Array f
  in
    unsafePartial $ Array.unsafeIndex arr i

asSizedF128 :: forall f. FVar f -> SizedF 128 (FVar f)
asSizedF128 = unsafeCoerce

asSizedF10 :: forall f. FVar f -> SizedF 10 (FVar f)
asSizedF10 = unsafeCoerce

-------------------------------------------------------------------------------
-- | Dummy points
-------------------------------------------------------------------------------

dummyVestaPt :: AffinePoint (F WrapField)
dummyVestaPt =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
  in
    { x: F g.x, y: F g.y }

dummyPallasPt :: AffinePoint (F StepField)
dummyPallasPt =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    { x: F g.x, y: F g.y }

dummyWrapSg :: AffinePoint StepField
dummyWrapSg =
  { x: fromBigInt $ unsafePartial fromJust $ BigInt.fromString "8063668238751197448664615329057427953229339439010717262869116690340613895496"
  , y: fromBigInt $ unsafePartial fromJust $ BigInt.fromString "2694491010813221541025626495812026140144933943906714931997499229912601205355"
  }

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

domainLog2 :: Int
domainLog2 = 16

stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

wrapEndo :: WrapField
wrapEndo = let EndoScalar e = endoScalar @Pallas.BaseField @WrapField in e

srsLengthLog2 :: Int
srsLengthLog2 = 16

wrapDomainLog2 :: Int
wrapDomainLog2 = 15

wrapSrsLengthLog2 :: Int
wrapSrsLengthLog2 = 15

-------------------------------------------------------------------------------
-- | Step VK derivation
-------------------------------------------------------------------------------

-- | Derive a step `VerifierIndex`'s commitments from a compiled step
-- | constraint system, returning a `StepVK (FVar WrapField)` ready to
-- | use as the `stepKeys` field in `WrapMainConfig`.
-- |
-- | This mirrors `Pickles.Prove.Step.stepCompile`'s
-- | `makeConstraintSystemWithPrevChallenges + createProverIndex +
-- | createVerifierIndex` tail, then runs `extractStepVKComms +
-- | stepVkForCircuit` on the result.
-- |
-- | Used by wrap-main circuit-diff fixtures (`WrapMainN2.purs` etc.)
-- | to obtain the SAME baked-in VK constants OCaml's
-- | `Pickles.compile_promise` produces, without importing anything from
-- | the OCaml side. The step CS is byte-identical to OCaml's, the SRS
-- | is the cached Vesta SRS, and the kimchi commitment algorithm is
-- | shared via FFI — so the resulting VK is byte-identical to OCaml's
-- | computed VK.
deriveStepVKFromCompiled
  :: forall @len
   . Reflectable len Int
  => CRS VestaG
  -> CompiledCircuit StepField
  -> StepVK (FVar WrapField)
deriveStepVKFromCompiled vestaSrs builtState =
  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem } = makeConstraintSystemWithPrevChallenges @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @len)
      }

    endo :: StepField
    endo = let EndoBase e = (endoBase :: EndoBase StepField) in e
    proverIndex = createProverIndex @StepField @VestaG
      { endo, constraintSystem, crs: vestaSrs }
    verifierIndex = createVerifierIndex @StepField @VestaG proverIndex
  in
    stepVkForCircuit (extractStepVKComms verifierIndex)

-- | Derive a wrap `VerifierIndex`'s commitments from a compiled wrap
-- | constraint system, returning a `VerificationKey
-- | (WeierstrassAffinePoint PallasG (F StepField))` ready to use as the
-- | per-slot known wrap key in `perSlotVkSources` (e.g.
-- | `ConstVk realNrrWrapVK` for Tree_proof_return's slot 0).
-- |
-- | Wrap-side analog of `deriveStepVKFromCompiled`. The wrap CS lives
-- | in `WrapField` over the Pallas curve; the commitments are Pallas
-- | points whose coordinates are in `Pallas.BaseField = StepField`, so
-- | the resulting VK is what a step circuit consumes when verifying
-- | the wrap proof.
-- |
-- | This mirrors the wrap-side compile pipeline:
-- | `makeConstraintSystemWithPrevChallenges + createProverIndex +
-- | createVerifierIndex`, then runs `extractWrapVKCommsAdvice` on the
-- | result. Used by Tree_proof_return to obtain the SAME baked-in wrap
-- | VK constants OCaml's `Pickles.compile_promise` produces for
-- | `No_recursion_return` (see
-- | `mina/src/lib/crypto/pickles/dump_tree_proof_return/dump_tree_proof_return.ml:50-83`,
-- | which compiles NRR up-front so its `compiled.wrap_key` is loaded
-- | when TPR's compile reads slot 0's prev tag).
deriveWrapVKFromCompiled
  :: forall @len
   . Reflectable len Int
  => CRS PallasG
  -> CompiledCircuit WrapField
  -> VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
deriveWrapVKFromCompiled pallasSrs builtState =
  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem } = makeConstraintSystemWithPrevChallenges @WrapField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @len)
      }

    endo :: WrapField
    endo = let EndoBase e = (endoBase :: EndoBase WrapField) in e
    proverIndex = createProverIndex @WrapField @PallasG
      { endo, constraintSystem, crs: pallasSrs }
    verifierIndex = createVerifierIndex @WrapField @PallasG proverIndex
  in
    extractWrapVKCommsAdvice verifierIndex

-------------------------------------------------------------------------------
-- | Compile-result artifacts
-- |
-- | Compile artifacts bundle a `CompiledCircuit` with the most-commonly
-- | needed *derived* fields (domain log2 from row count, wrap VK from
-- | commitments) so downstream compiles consume them as records rather
-- | than re-deriving from scratch.
-- |
-- | This is the test-side analog of OCaml's `Compiled.t` record
-- | (`compile.ml`'s output bundling `step_domains`, `wrap_domains`,
-- | `step_keys`, `wrap_key`). Eliminates the "hardcoded placeholder
-- | values" failure mode that bit several wrap-fixture tests when
-- | OCaml fixtures were regenerated from production drivers.
-------------------------------------------------------------------------------

type StepArtifact =
  { stepCs :: CompiledCircuit StepField
  , stepDomainLog2 :: Int
  }

type WrapArtifact =
  { stepCs :: CompiledCircuit StepField
  , stepDomainLog2 :: Int
  , wrapCs :: CompiledCircuit WrapField
  , wrapVk :: VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
  }

-- | Construct a `StepArtifact` from a compiled step CS, deriving the
-- | step domain log2 from the row count.
mkStepArtifact :: CompiledCircuit StepField -> StepArtifact
mkStepArtifact cs =
  { stepCs: cs
  , stepDomainLog2: domainLog2OfCompiled cs
  }

-- | Round up the constraint count to the next power-of-2 log. Mirrors
-- | OCaml's `Fix_domains.domains` row-count → log2 calculation
-- | (`compile.ml`), which sets the kimchi prover-index domain size.
domainLog2OfCompiled :: CompiledCircuit StepField -> Int
domainLog2OfCompiled builtState =
  let
    kimchiRows :: Array (KimchiRow StepField)
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    n = Array.length kimchiRows
  in
    ceilLog2 n
  where
  ceilLog2 :: Int -> Int
  ceilLog2 n
    | n <= 1 = 0
    | otherwise = go 0 1
        where
        go k acc = if acc >= n then k else go (k + 1) (acc * 2)

-- | Shape-pass + extract domain log2. For rules with self-prev slots
-- | whose own step domain log2 must be baked into their own
-- | `WrapMainConfig` — a self-circularity OCaml resolves with
-- | `Fix_domains.domains`' two-pass compile.
-- |
-- | Caller supplies a thunk that compiles the rule with ANY placeholder
-- | self log2 in `perSlotFopDomainLog2s`; we discard the resulting CS
-- | and read only its row count. The placeholder doesn't drift because
-- | it's never compared to anything.
preComputeSelfStepDomainLog2
  :: Effect (CompiledCircuit StepField) -> Effect Int
preComputeSelfStepDomainLog2 shapeCompile =
  domainLog2OfCompiled <$> shapeCompile
