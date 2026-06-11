module Test.Snarky.Circuit.Kimchi.EndoMul (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Maybe (fromJust)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (F(..), FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi.EndoMul (EndoRow, computeEndoChain, endo, endoInv)
import Snarky.Circuit.Kimchi.EndoScalar (expandToEndoScalar)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class PrimeField, class WeierstrassCurve, EndoBase(..), curveParams, endoBase, fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, arbitrary, withHelp)
import Test.QuickCheck.Gen (Gen, chooseInt, vectorOf)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

-- | The OLD per-round witness computation of `endo`, verbatim — the oracle
-- | `computeEndoChain` must reproduce field-element-for-field-element.
sequentialEndoRows
  :: forall f
   . PrimeField f
  => { xt :: f
     , yt :: f
     , eb :: f
     , acc0 :: AffinePoint f
     , bitRounds :: Array { b1 :: f, b2 :: f, b3 :: f, b4 :: f }
     }
  -> Array (EndoRow f)
sequentialEndoRows { xt, yt, eb, acc0, bitRounds } =
  _.out $ foldl step { acc: acc0, n: zero, out: [] } bitRounds
  where
  dbl v = v + v
  sq v = v * v
  step st { b1, b2, b3, b4 } =
    let
      AffinePoint { x: xp, y: yp } = st.acc
      xq1 = (one + (eb - one) * b1) * xt
      yq1 = (dbl b2 - one) * yt
      s1 = (yq1 - yp) / (xq1 - xp)
      s1Squared = sq s1
      s2 = (dbl yp / (dbl xp + xq1 - s1Squared)) - s1
      xr = xq1 + sq s2 - s1Squared
      yr = ((xp - xr) * s2) - yp
      xq2 = (one + (eb - one) * b3) * xt
      yq2 = (dbl b4 - one) * yt
      s3 = (yq2 - yr) / (xq2 - xr)
      s3Squared = sq s3
      s4 = (dbl yr / (dbl xr + xq2 - s3Squared)) - s3
      xs' = xq2 + sq s4 - s3Squared
      ys' = ((xr - xs') * s4) - yr
      n' = dbl (dbl (dbl (dbl st.n + b1) + b2) + b3) + b4
      row = { r: AffinePoint { x: xr, y: yr }, s1, s3, s: AffinePoint { x: xs', y: ys' }, nAccNext: n' }
    in
      { acc: AffinePoint { x: xs', y: ys' }, n: n', out: Array.snoc st.out row }

chainOracleSpec :: Spec Unit
chainOracleSpec =
  describe "batched endo witness chain" do
    it "computeEndoChain matches the sequential per-round formulas" $ quickCheck do
      base@(AffinePoint b') <- EC.genAffinePoint (Proxy @Vesta.G)
      nRounds <- chooseInt 0 20
      bools <- vectorOf nRounds (vectorOf 4 (arbitrary @Boolean))
      let
        EndoBase (eb :: Vesta.BaseField) = endoBase @Vesta.BaseField @Vesta.ScalarField
        params = curveParams (Proxy @Vesta.G)
        -- acc0 = 2·(g + φg), like the gadget's accInit
        phig = AffinePoint { x: eb * b'.x, y: b'.y }
        sumAff = unsafePartial $ fromJust $ EC.toAffine $ unsafePartial (EC.addAffine base phig)
        acc0 = coerce (EC.double params (coerce sumAff)) :: AffinePoint Vesta.BaseField
        toBit bb = if bb then one else zero :: Vesta.BaseField
        bitRounds = bools <#> \r -> case map toBit r of
          [ b1, b2, b3, b4 ] -> { b1, b2, b3, b4 }
          _ -> { b1: zero, b2: zero, b3: zero, b4: zero }
        inp = { xt: b'.x, yt: b'.y, eb, acc0, bitRounds }
      pure case computeEndoChain inp of
        Left e -> withHelp false ("computeEndoChain errored: " <> show e)
        Right rows -> withHelp (rows == sequentialEndoRows inp)
          "computeEndoChain /= sequential rows"

endoSpec
  :: forall f f' g g'
   . FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoSpec cfg _ curveProxy curveName =
  describe ("EndoMul " <> curveName) do
    it ("EndoMul circuit is valid for " <> curveName) $ unsafePartial $ do
      let
        f :: Tuple (AffinePoint f) (SizedF 128 (F f)) -> AffinePoint f
        f (Tuple (AffinePoint { x, y }) scalar) =
          let
            base = fromAffine @f @g { x, y }
            effectiveScalar = expandToEndoScalar scalar :: F f'
            result = scalarMul (unwrap effectiveScalar) base
            { x, y } = unsafePartial $ fromJust $ toAffine @f result
          in
            AffinePoint { x, y }

        circuit
          :: PrimeField f
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky f (KimchiConstraint f) () (AffinePoint (FVar f))
        circuit p scalar = do
          result <- endo @128 @32 p scalar
          pure result

        gen :: Gen (Tuple (AffinePoint f) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        (uncurry circuit)

      liftEffect $ verifyCircuit { s: builtState, gen, solver }

endoInvSpec
  :: forall f f' g g'
   . FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => HasEndo f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoInvSpec cfg _ curveProxy curveName =
  describe ("EndoInv " <> curveName) do
    it ("EndoInv circuit is valid for " <> curveName) $ unsafePartial $ do
      let
        -- Reference: compute g / scalar using constant operations
        refFn :: Tuple (AffinePoint f) (SizedF 128 (F f)) -> AffinePoint f
        refFn (Tuple (AffinePoint { x, y }) scalar) =
          let
            -- Convert scalar to effective scalar in f'
            effectiveScalar = expandToEndoScalar scalar :: F f'
            -- Compute inverse
            invScalar = recip effectiveScalar
            -- Scale the point
            base = fromAffine { x, y } :: g
            result = scalarMul (unwrap invScalar) base
            { x, y } = unsafePartial $ fromJust $ toAffine result
          in
            AffinePoint { x, y }

        circuit
          :: PrimeField f
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky f (KimchiConstraint f) () (AffinePoint (FVar f))
        circuit p scalar = endoInv @f @f' @g p scalar

        gen :: Gen (Tuple (AffinePoint f) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied refFn
            , input: QuickCheck 100 gen
            }
        )
        (uncurry circuit)

      liftEffect $ verifyCircuit { s: builtState, gen, solver }

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  chainOracleSpec
  endoSpec cfg (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoSpec cfg (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
  endoInvSpec cfg (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoInvSpec cfg (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
