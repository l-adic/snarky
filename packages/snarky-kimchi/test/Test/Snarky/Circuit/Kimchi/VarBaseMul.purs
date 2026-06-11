module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Kimchi.VarBaseMul (VbmRow, computeVbmChain, joinField, scaleFast1, scaleFast2, scaleFast2', splitField)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class PrimeField, curveParams, fromAffine, fromBigInt, fromInt, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (Type1, Type2(..), fieldSizeBits, fromShifted, toShifted)
import Test.QuickCheck (Result, arbitrary, withHelp, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, suchThat, vectorOf)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

-- | Scale a projective representative by a nonzero factor — same
-- | projective class, different coordinates.
scaleRep :: forall f. Semiring f => f -> EC.Point f -> EC.Point f
scaleRep k (EC.Point r) = EC.Point { x: k * r.x, y: k * r.y, z: k * r.z }

-- | The OLD per-bit witness computation of `varBaseMul`, verbatim — the
-- | oracle `computeVbmChain` must reproduce field-element-for-field-element.
sequentialVbmRows
  :: forall f
   . PrimeField f
  => { xBase :: f, yBase :: f, acc0 :: AffinePoint f, bits :: Array f }
  -> Array (VbmRow f)
sequentialVbmRows { xBase, yBase, acc0, bits } =
  _.out $ foldl step { acc: acc0, out: [] } bits
  where
  step { acc: AffinePoint a, out } b =
    let
      s1 = (a.y - yBase * ((b + b) - one)) / (a.x - xBase)
      s1Sq = s1 * s1
      s2 = ((a.y + a.y) / (a.x + a.x + xBase - s1Sq)) - s1
      xRes = xBase + s2 * s2 - s1Sq
      yRes = (a.x - xRes) * s2 - a.y
    in
      { acc: AffinePoint { x: xRes, y: yRes }, out: Array.snoc out { s1, s1Sq, s2, xRes, yRes } }

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  describe "batched witness chain (pure ops)" do
    it "batchInverse matches recip element-wise" $ quickCheck do
      xs <- Array.filter (_ /= zero) <$> arbitrary @(Array Vesta.BaseField)
      pure $ EC.batchInverse xs === map recip xs

    it "addProjectiveNonEqual matches affine addition on scaled representatives" $ quickCheck do
      p@(AffinePoint pa) <- EC.genAffinePoint (Proxy @Vesta.G)
      q <- EC.genAffinePoint (Proxy @Vesta.G) `suchThat` \(AffinePoint qa) -> qa.x /= pa.x
      k1 <- arbitrary @Vesta.BaseField `suchThat` (_ /= zero)
      k2 <- arbitrary @Vesta.BaseField `suchThat` (_ /= zero)
      let
        lhs = EC.toAffine $ EC.addProjectiveNonEqual (scaleRep k1 (EC.fromAffine p)) (scaleRep k2 (EC.fromAffine q))
        rhs = EC.toAffine $ unsafePartial (EC.addAffine p q)
      pure $ lhs === rhs

    it "doubleProjective matches affine doubling on scaled representatives" $ quickCheck do
      p <- EC.genAffinePoint (Proxy @Vesta.G)
      k <- arbitrary @Vesta.BaseField `suchThat` (_ /= zero)
      let
        params = curveParams (Proxy @Vesta.G)
        lhs = EC.toAffine $ EC.doubleProjective params (scaleRep k (EC.fromAffine p))
        rhs = Just (coerce (EC.double params (coerce p)) :: AffinePoint Vesta.BaseField)
      pure $ lhs === rhs

    it "computeVbmChain matches the sequential per-bit formulas" $ quickCheck do
      AffinePoint b' <- EC.genAffinePoint (Proxy @Vesta.G)
      nBits <- chooseInt 0 40
      bools <- vectorOf nBits (arbitrary @Boolean)
      let
        -- acc0 = 2·base, like the gadget's `addFast base base`
        g = fromAffine @Vesta.BaseField @Vesta.G { x: b'.x, y: b'.y }
        acc0r = unsafePartial $ fromJust $ toAffine @Vesta.BaseField (scalarMul (fromInt 2 :: Vesta.ScalarField) g)
        inp =
          { xBase: b'.x
          , yBase: b'.y
          , acc0: AffinePoint { x: acc0r.x, y: acc0r.y }
          , bits: map (\bb -> if bb then one else zero) bools
          }
      pure case computeVbmChain inp of
        Left e -> withHelp false ("computeVbmChain errored: " <> show e)
        Right rows -> rows === sequentialVbmRows inp

  describe "splitField / joinField" do
    it "roundtrips in Vesta.BaseField" $
      quickCheck (splitJoinRoundtrip @Vesta.BaseField)
    it "roundtrips in Vesta.ScalarField" $
      quickCheck (splitJoinRoundtrip @Vesta.ScalarField)

  -- Type1: Vesta circuit (field = Vesta.BaseField)
  -- Uses Vesta.G curve (coordinates in Vesta.BaseField = circuit field)
  -- Scalars are in Vesta.ScalarField (smaller than circuit field)
  describe "VarBaseMul Type1 (Vesta circuit)" do
    it "varBaseMul Circuit is Valid for Type1" $ unsafePartial do
      let
        f :: Tuple (AffinePoint Vesta.BaseField) (Type1 (F Vesta.BaseField)) -> AffinePoint Vesta.BaseField
        f (Tuple (AffinePoint { x, y }) scalar_) =
          let
            base = fromAffine @Vesta.BaseField @Vesta.G { x, y }
            scalar = case fromShifted scalar_ of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Vesta.BaseField result
          in
            AffinePoint { x: x', y: y' }

        circuit1
          :: PrimeField Vesta.BaseField
          => Tuple (AffinePoint (FVar Vesta.BaseField)) (Type1 (FVar Vesta.BaseField))
          -> Snarky Vesta.BaseField (KimchiConstraint Vesta.BaseField) () (AffinePoint (FVar Vesta.BaseField))
        circuit1 = uncurry \p t -> do
          g <- scaleFast1 @51 p t
          pure g

        gen :: Gen (Tuple (AffinePoint Vesta.BaseField) (Type1 (F Vesta.BaseField)))
        gen = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          -- Generate the shifted value directly in the circuit field
          -- (don't go through toShifted which crosses fields)
          t <- arbitrary @(F Vesta.ScalarField)
          pure $ Tuple p (toShifted t)

      { builtState, solver } <- circuitTest' @Vesta.BaseField
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        circuit1
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

  -- Type2: Pallas circuit, scalar field (Pallas.ScalarField) is LARGER than circuit field (Pallas.BaseField)
  describe "VarBaseMul Type2 (Pallas circuit)" do
    it "varBaseMul Circuit is Valid for Type2" $ unsafePartial do
      let
        f :: Tuple (AffinePoint Pallas.BaseField) { sDiv2 :: F Pallas.BaseField, sOdd :: Boolean } -> AffinePoint Pallas.BaseField
        f (Tuple (AffinePoint { x, y }) { sDiv2, sOdd }) =
          let
            base = fromAffine @Pallas.BaseField @Pallas.G { x, y }

            scalar :: Pallas.ScalarField
            scalar =
              let
                s :: Type2 (F Pallas.ScalarField)
                s = Type2 $ fromBigInt $ BigInt.fromInt 2 * toBigInt sDiv2 + if sOdd then one else zero
              in
                case fromShifted s of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField result
          in
            AffinePoint { x: x', y: y' }

        circuit2
          :: PrimeField Pallas.BaseField
          => Tuple (AffinePoint (FVar Pallas.BaseField)) { sDiv2 :: FVar Pallas.BaseField, sOdd :: BoolVar Pallas.BaseField }
          -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) () (AffinePoint (FVar Pallas.BaseField))
        circuit2 = uncurry \p t -> scaleFast2 @51 @254 p t

        gen :: Gen (Tuple (AffinePoint Pallas.BaseField) { sDiv2 :: F Pallas.BaseField, sOdd :: Boolean })
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          f_ <- arbitrary @(F Vesta.ScalarField)
          let
            Type2 sf = toShifted f_ :: Type2 (F Vesta.ScalarField)
            sDiv2 = toBigInt sf / BigInt.fromInt 2
            sOdd = BigInt.odd $ toBigInt sf
          pure $ Tuple p { sDiv2: fromBigInt @(F Pallas.BaseField) sDiv2, sOdd }

      { builtState, solver } <- circuitTest' @Pallas.BaseField
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        circuit2
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

  {-
    -- Forbidden Type2 values cause "Division by zero" in the Rust FFI during scalar multiplication
    -- (the forbidden value check constraints are added but the FFI computation fails first)
    it "rejects forbidden Type2 values" $ unsafePartial do
      let
        circuit2M
          :: forall r
           . PrimeField Pallas.BaseField
          => Tuple (AffinePoint (FVar Pallas.BaseField)) (Type2 (FVar Pallas.BaseField) (BoolVar Pallas.BaseField))
          -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) r (AffinePoint (FVar Pallas.BaseField))
        circuit2M = uncurry \p t -> scaleFast2 @51 @254 p t

        -- Generator that picks from forbidden values
        genForbidden :: Gen (Tuple (AffinePoint Pallas.BaseField) (Type2 (F Pallas.BaseField) Boolean))
        genForbidden = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          { sDiv2, sOdd } <- elements (fromJust $ NEA.fromArray forbiddenType2Values)
          pure $ Tuple p (Type2 { sDiv2, sOdd })

      -- Run in Effect to catch JS FFI exception as test failure
      try
        ( circuitTestM' @Pallas.BaseField identity
            cfg
            ( NEA.singleton
                { testFunction: (unsatisfied :: _ -> Expectation (AffinePoint Pallas.BaseField))
                , input: QuickCheck 10 genForbidden
                }
            )
            circuit2M
        ) >>= case _ of
        Left err | String.contains (String.Pattern "Division by zero") (message err) -> pure unit
        Left err -> fail $ "Unexpected error: " <> message err
        Right _ -> fail "Expected Division by zero error but test passed"
-}
  -- scaleFast2': takes a raw field element, splits it, then computes [s + 2^n] * base
  describe "VarBaseMul scaleFast2' (Pallas circuit)" do
    it "scaleFast2' circuit matches [s + 2^n] * base" $ unsafePartial do
      let
        -- Pure function: [s + 2^n] * base
        f :: Tuple (AffinePoint Pallas.BaseField) (F Pallas.BaseField) -> AffinePoint Pallas.BaseField
        f (Tuple (AffinePoint { x, y }) (F sVal)) =
          let
            base = fromAffine @Pallas.BaseField @Pallas.G { x, y }
            -- Convert base field element to scalar field with 2^n shift
            n = fieldSizeBits (Proxy @Pallas.BaseField)
            sBigInt = toBigInt sVal
            twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

            scalar :: Pallas.ScalarField
            scalar = fromBigInt (sBigInt + twoToN)
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField result
          in
            AffinePoint { x: x', y: y' }

        circuit3
          :: PrimeField Pallas.BaseField
          => Tuple (AffinePoint (FVar Pallas.BaseField)) (FVar Pallas.BaseField)
          -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) () (AffinePoint (FVar Pallas.BaseField))
        circuit3 = uncurry \p scalar -> scaleFast2' @51 @254 p scalar

        gen :: Gen (Tuple (AffinePoint Pallas.BaseField) (F Pallas.BaseField))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          scalar <- arbitrary @(F Pallas.BaseField)
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @Pallas.BaseField
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        circuit3
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

--------------------------------------------------------------------------------
-- splitField / joinField roundtrip (within same field)
--------------------------------------------------------------------------------

splitJoinRoundtrip :: forall @f. PrimeField f => F f -> Result
splitJoinRoundtrip x =
  let
    { sDiv2: F d, sOdd } = splitField x
    reconstructed = F (joinField { sDiv2: d, sOdd })
  in
    reconstructed === x
