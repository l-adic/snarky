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
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Types (StepField, WrapField)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Circuit.DSL (F(..), FVar, SizedF)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
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
