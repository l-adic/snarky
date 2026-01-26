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
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, add_, assertSquare_, const_, div_, exists, mul_, readCVar, scale_, sub_)
import Snarky.Circuit.DSL.Assert (assert_)
import Snarky.Circuit.DSL.Boolean (any_, if_)
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
  -- Witness: is x a quadratic residue?
  -- exists with Boolean return type automatically gives BoolVar
  isQRBool :: BoolVar f <- exists do
    F xVal <- readCVar x
    pure $ isSquare xVal

  -- Witness: sqrt of x (if QR) or sqrt of m*x (if not)
  sqrtVal <- exists do
    F xVal <- readCVar x
    let candidate = if isSquare xVal then xVal else nonResidue * xVal
    pure $ F $ fromMaybe' (\_ -> unsafeThrow "sqrtFlagged: neither x nor m*x is a quadratic residue") $ sqrt candidate

  -- Constraint: sqrtVal² = if isQR then x else m*x
  let mX = scale_ nonResidue x
  xOrMx <- if_ isQRBool x mX
  assertSquare_ sqrtVal xOrMx

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
  -- Compute potential x-coordinates
  -- t² requires mul_ (monadic)
  t2 <- mul_ t t

  -- alphaInv = (t² + f(u)) * t²
  let t2PlusFu = add_ t2 (const_ params.fu)
  alphaInv <- mul_ t2PlusFu t2

  -- alpha = 1 / alphaInv
  alpha <- div_ (const_ one) alphaInv

  -- t⁴ = t² * t²
  t4 <- mul_ t2 t2

  -- x1 = sqrtNeg3U2MinusUOver2 - t⁴ * alpha * sqrtNeg3U2
  t4Alpha <- mul_ t4 alpha
  temp1 <- mul_ t4Alpha (const_ params.sqrtNeg3U2)
  let x1 = sub_ (const_ params.sqrtNeg3U2MinusUOver2) temp1

  -- x2 = -u - x1
  let x2 = sub_ (const_ (negate params.u)) x1

  -- x3 = u - (t² + f(u))² * (1/t²) * (1/(3u²))
  -- Note: t2Inv = alpha * (t² + fu) = 1/t² (since alpha = 1/((t²+fu)*t²))
  t2Inv <- mul_ alpha t2PlusFu
  t2PlusFuSq <- mul_ t2PlusFu t2PlusFu
  temp2a <- mul_ t2PlusFuSq t2Inv
  temp2 <- mul_ temp2a (const_ params.inv3U2)
  let x3 = sub_ (const_ params.u) temp2

  -- y² for each candidate x: y² = x³ + b
  let
    ySquared x = do
      xSq <- mul_ x x
      xCu <- mul_ xSq x
      pure $ add_ xCu (const_ params.b)

  -- Try sqrt for each candidate
  y1Sq <- ySquared x1
  y2Sq <- ySquared x2
  y3Sq <- ySquared x3
  { sqrtVal: y1, isQR: b1 } <- sqrtFlagged params.nonResidue y1Sq
  { sqrtVal: y2, isQR: b2 } <- sqrtFlagged params.nonResidue y2Sq
  { sqrtVal: y3, isQR: b3 } <- sqrtFlagged params.nonResidue y3Sq

  -- Assert at least one is a valid point
  assert_ =<< any_ [ b1, b2, b3 ]

  -- Select the first valid point: if b1 then (x1,y1) else if b2 then (x2,y2) else (x3,y3)
  xInner <- if_ b2 x2 x3
  xResult <- if_ b1 x1 xInner

  yInner <- if_ b2 y2 y3
  yResult <- if_ b1 y1 yInner

  pure { x: xResult, y: yResult }
