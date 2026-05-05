module Pickles.CircuitDiffs.PureScript.Common
  ( CompiledCircuit
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
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Prove.Wrap (extractStepVKComms, stepVkForCircuit)
import Pickles.Types (StepField, WrapField)
import Pickles.VerificationKey (StepVK)
import Prim.Int (class Add)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges)
import Snarky.Backend.Kimchi.Class (createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar, SizedF)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), class ToKimchiRows, toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), EndoScalar(..), endoBase, endoScalar, fromBigInt, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
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
  :: forall @len lenPred
   . Reflectable len Int
  => Add 1 lenPred len
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
