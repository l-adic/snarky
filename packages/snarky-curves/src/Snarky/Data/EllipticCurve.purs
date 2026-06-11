module Snarky.Data.EllipticCurve
  ( CurveParams
  , AffinePoint(..)
  , genAffinePoint
  , Point(..)
  , DoubleAddRow
  , addAffine
  , addProjectiveNonEqual
  , batchInverse
  , doubleAddChain
  , doubleProjective
  , fromAffine
  , genPoint
  , mkPoint
  , toAffine
  , double
  , negate_
  , WeierstrassAffinePoint(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust, isJust)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Circuit.DSL (class AssertEqual, class BasicSystem, class CheckedType, class CircuitType, class IfThenElse, EvaluationError(..), F(..), FVar, add_, assertEqGeneric, assertSquare_, const_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, if_, isEqualGeneric, mul_, scale_, square_)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Class as Snarky.Curves.Class
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy(..))

type CurveParams f = { a :: f, b :: f }

newtype AffinePoint f = AffinePoint { x :: f, y :: f }

derive instance Newtype (AffinePoint f) _
derive instance Generic (AffinePoint f) _
derive newtype instance Eq f => Eq (AffinePoint f)
derive newtype instance Ord f => Ord (AffinePoint f)
derive newtype instance Show f => Show (AffinePoint f)
derive newtype instance Arbitrary f => Arbitrary (AffinePoint f)
derive instance Functor AffinePoint

-- | JSON codecs delegate to the inner `{ x, y }` record (the record had
-- | these — and `Ord`/`Arbitrary` — for free before `AffinePoint` became a
-- | newtype).
derive newtype instance WriteForeign f => WriteForeign (AffinePoint f)
derive newtype instance ReadForeign f => ReadForeign (AffinePoint f)

-- | Value side is the raw field `f`; `F f` is only the internal leaf
-- | marker the generic deriving needs (reached by `coerce`).
instance CircuitType f (AffinePoint f) (AffinePoint (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy :: Proxy (AffinePoint (F f)))
  valueToFields a = genericValueToFields (coerce a :: AffinePoint (F f))
  fieldsToValue fs = coerce (genericFieldsToValue fs :: AffinePoint (F f))
  varToFields = genericVarToFields @(AffinePoint (F f))
  fieldsToVar = genericFieldsToVar @(AffinePoint (F f))

instance CheckedType f c (AffinePoint (FVar f)) where
  check = genericCheck

instance AssertEqual f c (AffinePoint (FVar f)) where
  assertEq = assertEqGeneric
  isEqual = isEqualGeneric

instance IfThenElse f c (AffinePoint (FVar f)) where
  if_ b (AffinePoint t) (AffinePoint e) = AffinePoint <$> if_ b t e

genAffinePoint
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Gen (AffinePoint f)
genAffinePoint _ = do
  mp <- (Snarky.Curves.Class.toAffine @f @g <$> arbitrary) `suchThat` isJust
  let { x, y } = unsafePartial $ fromJust mp
  pure (AffinePoint { x, y })

newtype Point f = Point { x :: f, y :: f, z :: f }

derive instance Generic (Point f) _

instance (PrimeField f) => Show (Point f) where
  show p = case toAffine p of
    Nothing -> show $ { x: zero @f, y: one @f, z: one @f }
    Just (AffinePoint { x, y }) -> show { x, y, z: one @f }

instance CircuitType f (Point f) (Point (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy :: Proxy (Point (F f)))
  valueToFields a = genericValueToFields (coerce a :: Point (F f))
  fieldsToValue fs = coerce (genericFieldsToValue fs :: Point (F f))
  varToFields = genericVarToFields @(Point (F f))
  fieldsToVar = genericFieldsToVar @(Point (F f))

instance CheckedType f c (Point (FVar f)) where
  check = genericCheck

genPoint
  :: forall f g
   . WeierstrassCurve f g
  => Arbitrary g
  => Proxy g
  -> Gen (Point (F f))
genPoint _ =
  arbitrary @g <#> \g ->
    case Snarky.Curves.Class.toAffine g of
      Just { x, y } -> Point { x: F x, y: F y, z: one }
      Nothing -> infinity_

mkPoint
  :: forall f
   . PrimeField f
  => CurveParams f
  -> { x :: f
     , y :: f
     , z :: f
     }
  -> Maybe (Point f)
mkPoint { a, b } p@{ x, y, z }
  | z == zero && x == zero && y == one = Just infinity_
  | z /= zero && y * y == x * x * x + a * x + b = Just (Point p)
  | otherwise = Nothing

toAffine :: forall f. PrimeField f => Point f -> Maybe (AffinePoint f)
toAffine (Point { x, y, z })
  | z == zero = Nothing
  | otherwise = Just (AffinePoint { x: x / z, y: y / z })

fromAffine :: forall f. PrimeField f => AffinePoint f -> Point f
fromAffine (AffinePoint { x, y }) = Point { x, y, z: one }

instance PrimeField f => Eq (Point f) where
  eq (Point p1) (Point p2)
    | (p1.z /= zero && p2.z /= zero) =
        (p1.x / p1.z) == (p2.x / p2.z) &&
          (p2.y / p2.z) == (p2.y / p2.z)
    | p1.z == zero && p2.z == zero =
        p1.x == zero && p2.x == zero
    | otherwise = false

infinity_ :: forall f. PrimeField f => Point f
infinity_ = Point { x: zero, y: one, z: zero }

double :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> AffinePoint (F f)
double { a } (AffinePoint { x, y }) =
  let
    lambda = (three * x * x + F a) / (two * y)
    x' = lambda * lambda - two * x
    y' = lambda * (x - x') - y
    two = F (one + one)
    three = F (one + one + one)
  in
    AffinePoint { x: x', y: y' }

negate_
  :: forall f
   . PrimeField f
  => AffinePoint f
  -> AffinePoint f
negate_ (AffinePoint { x, y }) = AffinePoint { x, y: negate y }

addAffine
  :: forall f
   . Partial
  => PrimeField f
  => AffinePoint f
  -> AffinePoint f
  -> Point f
addAffine (AffinePoint p1) (AffinePoint p2)
  | p1.x == p2.x && p1.y == negate p2.y = infinity_
  | otherwise =
      let
        { x, y } = unsafeAdd p1 p2
      in
        Point { x, y, z: one }
      where
      unsafeAdd { x: x1, y: y1 } { x: x2, y: y2 } =
        let
          lambda = (y2 - y1) / (x2 - x1)
          x3 = (lambda * lambda) - x1 - x2
          y3 = lambda * (x1 - x3) - y1
        in
          { x: x3, y: y3 }

-- | Invert every element of an array paying a SINGLE field inversion
-- | (plus ~4n multiplications) instead of n inversions — Montgomery's
-- | trick, in the prefix/suffix-product formulation:
-- |
-- |   xᵢ⁻¹ = (x₀·…·xᵢ₋₁) · (xᵢ₊₁·…·xₙ₋₁) · (x₀·…·xₙ₋₁)⁻¹
-- |
-- | PRECONDITION: every element is nonzero (a zero poisons the shared
-- | product). Callers check denominators — and report their own
-- | domain-specific error — before batching.
batchInverse :: forall f. PrimeField f => Array f -> Array f
batchInverse xs
  | Array.null xs = []
  | otherwise =
      let
        n = Array.length xs
        prefixes = Array.scanl (*) one xs -- prefixes !! i = x₀·…·xᵢ
        suffixes = Array.scanr (*) one xs -- suffixes !! i = xᵢ·…·xₙ₋₁
        ix arr i = unsafePartial (Array.unsafeIndex arr i)
        totalInv = recip (ix prefixes (n - 1))
      in
        Array.mapWithIndex
          ( \i _ ->
              let
                pre = if i == 0 then one else ix prefixes (i - 1)
                suf = if i == n - 1 then one else ix suffixes (i + 1)
              in
                pre * suf * totalInv
          )
          xs

-- | Projective (homogeneous-coordinate) doubling — division-free.
-- | EFD `dbl-2007-bl` for short Weierstrass y²z = x³ + axz² + bz³.
-- | Total: handles infinity and 2-torsion (y = 0 ⇒ result at infinity).
doubleProjective :: forall f. PrimeField f => CurveParams f -> Point f -> Point f
doubleProjective { a } pt@(Point { x, y, z })
  | z == zero = pt
  | otherwise =
      let
        two v = v + v
        xx = x * x
        zz = z * z
        w = a * zz + (xx + xx + xx)
        s = two (y * z)
        ss = s * s
        sss = s * ss
        r = y * s
        rr = r * r
        xr = x + r
        b' = xr * xr - xx - rr
        h = w * w - two b'
      in
        Point { x: h * s, y: w * (b' - h) - two rr, z: sss }

-- | Projective (homogeneous-coordinate) addition core — division-free.
-- | EFD `add-1998-cmo-2`. No doubling fallback (and hence no curve
-- | params): if the two inputs share an x-coordinate (equal or inverse
-- | points), the result has `z == 0` — callers either pre-exclude that
-- | case or detect it on the output. Infinity inputs pass through.
addProjectiveNonEqual :: forall f. PrimeField f => Point f -> Point f -> Point f
addProjectiveNonEqual p1@(Point { x: x1, y: y1, z: z1 }) p2@(Point { x: x2, y: y2, z: z2 })
  | z1 == zero = p2
  | z2 == zero = p1
  | otherwise =
      let
        two v' = v' + v'
        y1z2 = y1 * z2
        x1z2 = x1 * z2
        z1z2 = z1 * z2
        u = y2 * z1 - y1z2
        v = x2 * z1 - x1z2
        uu = u * u
        vv = v * v
        vvv = v * vv
        r = vv * x1z2
        aa = uu * z1z2 - vvv - two r
      in
        Point { x: v * aa, y: u * (r - aa) - vvv * y1z2, z: vvv * z1z2 }

-- | Per-step witness row of a "double-add" scalar-mul gadget — the five
-- | values its exists bodies witness for one step `acc' = 2·acc + Q`.
type DoubleAddRow f = { s1 :: f, s1Sq :: f, s2 :: f, xRes :: f, yRes :: f }

-- | The entire witness chain of a double-add scalar multiplication with
-- | THREE field inversions total (instead of two PER STEP): walk
-- | `acc_{i+1} = 2·acc_i + Q_i` in projective coordinates (division-free),
-- | then recover affine coordinates and slopes with `batchInverse`
-- | (Montgomery's trick).
-- |
-- | The rows are the SAME field elements the sequential per-step bodies
-- | produce — the slope formulas below are theirs with `/ d` replaced by
-- | `* dInv` (a field's inverse is unique, and `(-a)·(-b)⁻¹ = a·b⁻¹`
-- | exactly, so either chord-slope sign spelling lands on the same
-- | element). Per-step degeneracies are checked in chain order, reported
-- | as `DivisionByZero` under the caller's context:
-- |   * `xAcc == xQ` (the s1 denominator) ⇔ `X == xQ·Z`, checked before
-- |     each step;
-- |   * `2·xAcc + xQ − s1² == 0` (the s2 denominator) ⇔ the step result
-- |     lands at infinity ⇔ `z == 0` after the step.
doubleAddChain
  :: forall f
   . PrimeField f
  => String
  -> AffinePoint f
  -> Array (AffinePoint f)
  -> Either EvaluationError (Array (DoubleAddRow f))
doubleAddChain context acc0 qs = do
  -- Phase 1: projective walk; record each step's input accumulator.
  inputs <- _.out <$> foldM step { accP: fromAffine acc0, out: [] } qs
  let
    -- Phase 2: batch-normalize the projective accumulators.
    zInvs = batchInverse (map (\r -> let Point pp = r.accP in pp.z) inputs)
    affs = Array.zipWith
      (\r zInv -> let Point pp = r.accP in { xAcc: pp.x * zInv, yAcc: pp.y * zInv, q: r.q })
      inputs
      zInvs
    -- Phase 3: slopes via two more batches (denominators nonzero by the
    -- phase-1 checks).
    dInvs = batchInverse (map (\r -> let AffinePoint q = r.q in q.x - r.xAcc) affs)
    s1s = Array.zipWith (\r dInv -> let AffinePoint q = r.q in (q.y - r.yAcc) * dInv) affs dInvs
    eInvs = batchInverse
      (Array.zipWith (\r s1 -> let AffinePoint q = r.q in dbl r.xAcc + q.x - s1 * s1) affs s1s)
  pure $ Array.zipWith
    ( \(Tuple r s1) eInv ->
        let
          AffinePoint q = r.q
          s1Sq = s1 * s1
          s2 = dbl r.yAcc * eInv - s1
          xRes = q.x + s2 * s2 - s1Sq
          yRes = (r.xAcc - xRes) * s2 - r.yAcc
        in
          { s1, s1Sq, s2, xRes, yRes }
    )
    (Array.zip affs s1s)
    eInvs
  where
  dbl v = v + v
  step st q@(AffinePoint qr) = do
    let Point pp = st.accP
    when (pp.x == qr.x * pp.z) $ Left $ DivisionByZero
      { context, expression: Just "xAcc - xQ" }
    let
      accP' = addProjectiveNonEqual (addProjectiveNonEqual st.accP (fromAffine q)) st.accP
      Point pp' = accP'
    when (pp'.z == zero) $ Left $ DivisionByZero
      { context, expression: Just "2*xAcc + xQ - s1^2" }
    pure { accP: accP', out: Array.snoc st.out { accP: st.accP, q } }

newtype WeierstrassAffinePoint :: Type -> Type -> Type
newtype WeierstrassAffinePoint g f = WeierstrassAffinePoint { x :: f, y :: f }

derive instance Generic (WeierstrassAffinePoint g f) _

-- | NOTE: `WeierstrassAffinePoint` keeps its value side `F`-leaved (unlike
-- | `Point`/`AffinePoint`, which drop `F`). It is composed inside pickles'
-- | generic-derived `PerProofWitness`/`ProofState` *under a shared type param*
-- | that is also used for bare scalar leaves (`Vector ds f`). One shared param
-- | can't be raw `f` for the point and `F f` for the leaves at once, so WAP
-- | must match the leaves and stay `F`-leaved.
instance CircuitType f (WeierstrassAffinePoint g (F f)) (WeierstrassAffinePoint g (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(WeierstrassAffinePoint g (F f))
  fieldsToVar = genericFieldsToVar @(WeierstrassAffinePoint g (F f))

instance (PrimeField f, BasicSystem f c, WeierstrassCurve f g) => CheckedType f c (WeierstrassAffinePoint g (FVar f)) where
  -- | assert_on_curve: y² = x³ + ax + b
  -- | Matches OCaml's snarky_curve.ml assert_on_curve exactly:
  -- |   x2 = square x; x3 = x2 * x; assert_square y (x3 + ax + b)
  -- | Uses square_ (not mul_ x x) to match OCaml's Square constraint (cm=1, co=-1).
  -- | x2*x is built as a compound CVar via mul_ (witnessing x3),
  -- | then assert_square embeds the rhs expression into a single constraint.
  check (WeierstrassAffinePoint { x, y }) = do
    let { a, b } = curveParams (Proxy @g)
    x2 <- square_ x
    x3 <- mul_ x2 x
    assertSquare_ y (x3 `add_` scale_ a x `add_` const_ b)