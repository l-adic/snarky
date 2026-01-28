module Test.Pickles.BulletproofVerifier where

-- | Tests for bulletproof verifier circuits.
-- | Verifies that combineSplitCommitments produces correct output.

import Prelude

import Data.Foldable (foldl)
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..), uncurry)
import Data.Vector (Vector, reverse, uncons)
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.BulletproofVerifier (combineSplitCommitments)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldConstant)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class WeierstrassCurve, endoScalar, fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Generate a 128-bit field element (for endo scalar)
gen128BitElem :: forall f n _l. FieldSizeInBits f n => Reflectable _l Int => Add 128 _l n => Gen (F f)
gen128BitElem = do
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

-- | Test size for combineSplitCommitments
-- | Use small vector to keep constraint count manageable
type TestCommitmentCount = 4

spec :: Spec Unit
spec = describe "Pickles.BulletproofVerifier" do
  describe "combineSplitCommitments" do
    combineSplitCommitmentsSpec
      (Proxy @Vesta.BaseField)
      (Proxy @Pallas.BaseField)
      (Proxy @Vesta.G)
      "Pallas (over Vesta.BaseField)"
    combineSplitCommitmentsSpec
      (Proxy @Pallas.BaseField)
      (Proxy @Vesta.BaseField)
      (Proxy @Pallas.G)
      "Vesta (over Pallas.BaseField)"

-- | Test combineSplitCommitments circuit
-- | f = circuit field (coordinates), f' = scalar field, g = curve group
combineSplitCommitmentsSpec
  :: forall f f' g g'
   . FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => PoseidonField f
  => HasEndo f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => Proxy f
  -> Proxy f'
  -> Proxy g
  -> String
  -> Spec Unit
combineSplitCommitmentsSpec _ _ curveProxy curveName =
  it ("combineSplitCommitments matches reference for " <> curveName) $ unsafePartial do
    let
      -- Reference function: Horner's method with pure scalar mul
      -- c_0 + xi * (c_1 + xi * (c_2 + ... + xi * c_{n-1}))
      refFn :: Tuple (F f) (Vector TestCommitmentCount (AffinePoint (F f))) -> AffinePoint (F f)
      refFn (Tuple (F xi) commitments) =
        let
          -- Convert xi to scalar field f' for scalarMul
          effectiveXi :: f'
          effectiveXi = toFieldConstant (coerceViaBits xi) (endoScalar :: f')

          -- Convert affine points to projective for computation
          toProj { x: F px, y: F py } = fromAffine @f @g { x: px, y: py }
          fromProj p =
            let
              { x, y } = unsafePartial $ fromJust $ toAffine @f p
            in
              { x: F x, y: F y }

          -- Horner: start from last, fold back
          reversed = reverse commitments
          { head, tail } = uncons reversed
          result = foldl
            (\acc c -> scalarMul effectiveXi acc <> toProj c)
            (toProj head)
            tail
        in
          fromProj result

      solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

      circuit
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => FVar f
        -> Vector TestCommitmentCount (AffinePoint (FVar f))
        -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
      circuit = combineSplitCommitments @TestCommitmentCount

      s = compilePure
        (Proxy @(Tuple (F f) (Vector TestCommitmentCount (AffinePoint (F f)))))
        (Proxy @(AffinePoint (F f)))
        (Proxy @(KimchiConstraint f))
        (uncurry circuit)
        Kimchi.initialState

      gen :: Gen (Tuple (F f) (Vector TestCommitmentCount (AffinePoint (F f))))
      gen = do
        xi <- gen128BitElem
        commitments <- Vector.generator (Proxy @TestCommitmentCount) (EC.genAffinePoint curveProxy)
        pure $ Tuple xi commitments

    circuitSpecPure' 10
      { builtState: s
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied refFn
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ verifyCircuit { s, gen, solver }
  where
  coerceViaBits :: f -> f'
  coerceViaBits = packPure <<< unpackPure
