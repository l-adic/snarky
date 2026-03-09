-- | BW19 Hash-to-Curve algorithm (Wahby-Boneh 2019)
-- | Maps a field element to a point on a Weierstrass curve y² = x³ + b (a=0)
-- |
-- | Reference: https://eprint.iacr.org/2019/403
-- | Mina implementation: mina/src/lib/snarky/group_map/bw19.ml
module Snarky.Circuit.Kimchi.GroupMap
  ( GroupMapParams
  , groupMapParams
  , potentialXs
  , groupMap
  , groupMapCircuit
  ) where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (fromMaybe')
import Effect.Exception.Unsafe (unsafeThrow)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, add_, and_, assertNonZero_, assertSquare_, const_, div_, exists, if_, label, mul_, not_, readCVar, scale_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasBW19, class HasSqrt, class PrimeField, bw19Params, curveParams, fromInt, isSquare, sqrt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy)

-- | Full parameters needed for group map circuit
-- | Combines FFI BW19 params with curve params and a computed non-residue
type GroupMapParams f =
  { u :: f -- First valid u where u ≠ 0 and f(u) ≠ 0
  , fu :: f -- f(u) = u³ + b
  , sqrtNeg3U2MinusUOver2 :: f -- (sqrt(-3u²) - u) / 2
  , sqrtNeg3U2 :: f -- sqrt(-3u²)
  , inv3U2 :: f -- 1 / (3u²)
  , b :: f -- Curve parameter b
  , nonResidue :: f -- A known quadratic non-residue
  }

-- | Build GroupMapParams from HasBW19 FFI params and curve params
-- | The nonResidue is found by searching from 2
groupMapParams
  :: forall f g
   . HasSqrt f
  => HasBW19 f g
  => Proxy g
  -> GroupMapParams f
groupMapParams proxy =
  let
    bw19 = bw19Params proxy
    { b } = curveParams proxy

    -- Find first non-residue (first non-square starting from 2)
    findNonResidue i =
      if not (isSquare i) then i else findNonResidue (i + one)
    nonResidue = findNonResidue (fromInt @f 2)
  in
    { u: bw19.u
    , fu: bw19.fu
    , sqrtNeg3U2MinusUOver2: bw19.sqrtNeg3U2MinusUOver2
    , sqrtNeg3U2: bw19.sqrtNeg3U2
    , inv3U2: bw19.inv3U2
    , b
    , nonResidue
    }

-- | Compute three potential x-coordinates for the group map
-- | One of these will have y² = x³ + b being a quadratic residue
potentialXs
  :: forall f
   . PrimeField f
  => GroupMapParams f
  -> f
  -> { x1 :: f, x2 :: f, x3 :: f }
potentialXs params t =
  let
    t2 = t * t
    alphaInv = (t2 + params.fu) * t2
    alpha = one / alphaInv

    t4 = t2 * t2
    x1 = params.sqrtNeg3U2MinusUOver2 - t4 * alpha * params.sqrtNeg3U2
    x2 = negate params.u - x1

    t2PlusFu = t2 + params.fu
    t2Inv = alpha * t2PlusFu -- = 1/t²
    x3 = params.u - (t2PlusFu * t2PlusFu) * t2Inv * params.inv3U2
  in
    { x1, x2, x3 }

-- | Pure groupMap: maps a field element to a curve point
-- | For witness generation, not for in-circuit use
groupMap
  :: forall f
   . HasSqrt f
  => GroupMapParams f
  -> f
  -> AffinePoint f
groupMap params t =
  let
    ySquared x = x * x * x + params.b

    { x1, x2, x3 } = potentialXs params t

    tryDecode x = sqrt (ySquared x) <#> \y -> { x, y }
  in
    fromMaybe' (\_ -> unsafeThrow "groupMap: no valid x-coordinate found (BW19 invariant violated)")
      $ tryDecode x1 <|> tryDecode x2 <|> tryDecode x3

-- | In-circuit sqrt with flag indicating if input is a quadratic residue
-- | Uses the trick: exists is_square, y such that y² = if is_square then x else m*x
-- | where m is a known non-residue
sqrtFlagged
  :: forall f t m
   . PrimeField f
  => HasSqrt f
  => CircuitM f (KimchiConstraint f) t m
  => f -- non-residue constant
  -> FVar f
  -> Snarky (KimchiConstraint f) t m { sqrtVal :: FVar f, isQR :: BoolVar f }
sqrtFlagged nonResidue x = do
  isQRBool :: BoolVar f <- label "sf_exists_bool" $ exists do
    F xVal <- readCVar x
    pure $ isSquare xVal

  let mX = scale_ nonResidue x
  xOrMx <- label "sf_if" $ if_ isQRBool x mX

  sqrtVal <- label "sf_exists_sqrt" $ exists do
    F xOrMxVal <- readCVar xOrMx
    pure $ F $ fromMaybe' (\_ -> unsafeThrow "sqrtFlagged: neither x nor m*x is a quadratic residue") $ sqrt xOrMxVal

  label "sf_assertSq" $ assertSquare_ sqrtVal xOrMx

  pure { sqrtVal, isQR: isQRBool }

-- | In-circuit group map
-- | Maps a field element to a curve point using the BW19 algorithm
groupMapCircuit
  :: forall f t m
   . HasSqrt f
  => CircuitM f (KimchiConstraint f) t m
  => GroupMapParams f
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
groupMapCircuit params t = do
  t2 <- label "t2" $ mul_ t t
  let t2PlusFu = add_ t2 (const_ params.fu)
  alphaInv <- label "alphaInv" $ mul_ t2PlusFu t2
  alpha <- label "alpha" $ div_ (const_ one) alphaInv
  t4 <- label "t4" $ mul_ t2 t2
  t4Alpha <- label "t4Alpha" $ mul_ t4 alpha
  temp1 <- label "temp1" $ mul_ t4Alpha (const_ params.sqrtNeg3U2)
  let x1 = sub_ (const_ params.sqrtNeg3U2MinusUOver2) temp1
  let x2 = sub_ (const_ (negate params.u)) x1
  t2Inv <- label "t2Inv" $ mul_ alpha t2PlusFu
  t2PlusFuSq <- label "t2PlusFuSq" $ mul_ t2PlusFu t2PlusFu
  temp2a <- label "temp2a" $ mul_ t2PlusFuSq t2Inv
  temp2 <- label "temp2" $ mul_ temp2a (const_ params.inv3U2)
  let x3 = sub_ (const_ params.u) temp2

  let
    ySquared lbl x = label lbl do
      xSq <- label "xSq" $ mul_ x x
      xCu <- label "xCu" $ mul_ xSq x
      pure $ add_ xCu (const_ params.b)

  y1Sq <- ySquared "ySq1" x1
  { sqrtVal: y1, isQR: b1 } <- label "sf1" $ sqrtFlagged params.nonResidue y1Sq
  y2Sq <- ySquared "ySq2" x2
  { sqrtVal: y2, isQR: b2 } <- label "sf2" $ sqrtFlagged params.nonResidue y2Sq
  y3Sq <- ySquared "ySq3" x3
  { sqrtVal: y3, isQR: b3 } <- label "sf3" $ sqrtFlagged params.nonResidue y3Sq

  label "assertAny" $ assertNonZero_ (coerce b1 `add_` coerce b2 `add_` (coerce b3 :: FVar f))

  let nb1 = not_ b1
  x2_is_first <- label "x2first" $ nb1 `and_` b2
  -- OCaml's && is right-associative: (not b1) && ((not b2) && b3)
  nb2_and_b3 <- label "nb2b3" $ (not_ b2) `and_` b3
  x3_is_first <- label "x3first" $ nb1 `and_` nb2_and_b3

  t3y <- label "t3y" $ mul_ (coerce x3_is_first) y3
  t2y <- label "t2y" $ mul_ (coerce x2_is_first) y2
  t1y <- label "t1y" $ mul_ (coerce b1) y1
  let yResult = add_ (add_ t1y t2y) t3y

  t3x <- label "t3x" $ mul_ (coerce x3_is_first) x3
  t2x <- label "t2x" $ mul_ (coerce x2_is_first) x2
  t1x <- label "t1x" $ mul_ (coerce b1) x1
  let xResult = add_ (add_ t1x t2x) t3x

  pure { x: xResult, y: yResult }
