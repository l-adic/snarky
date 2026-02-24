module Test.Pickles.MultiscaleKnown where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Traversable (for_)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.MultiscaleKnown (multiscaleKnown)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (curveParams, fromAffine, fromBigInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (chooseInt, randomSample')
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
import Test.Spec (Spec, before, describe, it)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

params :: { a :: Pallas.BaseField, b :: Pallas.BaseField }
params = curveParams (Proxy @Pallas.G)

-- | Make a base point: [i]*G on Pallas
mkBase :: Int -> AffinePoint (F Pallas.BaseField)
mkBase i = unsafePartial $
  let
    scalar = fromBigInt (BigInt.fromInt i) :: Pallas.ScalarField
    { x, y } = fromJust $ toAffine @Pallas.BaseField (scalarMul scalar (generator :: Pallas.G))
  in
    { x: F x, y: F y }

-- | Pure reference: interpret circuit field scalars as integers, do group-level scalar mul
pureMultiscale
  :: Array { scalar :: F Pallas.BaseField, base :: AffinePoint (F Pallas.BaseField) }
  -> AffinePoint (F Pallas.BaseField)
pureMultiscale terms = unsafePartial $
  let
    affineResults = map
      ( \{ scalar: F s, base: { x: F px, y: F py } } ->
          let
            scalarFq = fromBigInt (toBigInt s) :: Pallas.ScalarField
          in
            fromJust $ toAffine @Pallas.BaseField $ scalarMul scalarFq (fromAffine { x: px, y: py } :: Pallas.G)
      )
      terms
    { head, tail } = fromJust $ Array.uncons affineResults
    summed = Array.foldl
      (\acc p -> fromJust $ EC.toAffine $ EC.addAffine acc p)
      head
      tail
  in
    { x: F summed.x, y: F summed.y }

spec :: Spec Unit
spec = do
  describe "MultiscaleKnown" do
    before genLengths $ it "variable number of terms" \ns ->
      for_ ns \numTerms -> do
        Console.log $ "Testing with " <> show numTerms <> " terms"
        reifyType numTerms \pn ->
          multiscaleKnownTest pn

genLengths :: Aff (Array Int)
genLengths = liftEffect do
  ns <- randomSample' 3 $ chooseInt 3 10
  pure $ Array.nub $ [ 1, 2 ] <> ns

multiscaleKnownTest
  :: forall numTerms
   . Reflectable numTerms Int
  => Proxy numTerms
  -> Aff Unit
multiscaleKnownTest pn = do
  let
    n = reflectType pn
    bases = map mkBase (Array.range 1 n)

    pureFn :: Vector numTerms (F Pallas.BaseField) -> AffinePoint (F Pallas.BaseField)
    pureFn scalars = pureMultiscale $
      Array.zipWith (\scalar base -> { scalar, base })
        (Vector.toUnfoldable scalars)
        bases

    circuit'
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => Vector numTerms (FVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (AffinePoint (FVar Pallas.BaseField))
    circuit' scalars = multiscaleKnown @51 @254 params
      $ unsafePartial fromJust
      $ NEA.fromArray
      $
        Array.zipWith (\scalar base -> { scalar, base })
          (Vector.toUnfoldable scalars)
          bases

    gen = Vector.generator pn arbitrary

  { builtState: s, solver } <- circuitTest' @Pallas.BaseField 5
    kimchiTestConfig
    (NEA.singleton { testFunction: satisfied pureFn, gen })
    circuit'
  liftEffect $ verifyCircuit { s, gen, solver }
