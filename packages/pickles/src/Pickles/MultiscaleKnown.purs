module Pickles.MultiscaleKnown (multiscaleKnown) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (foldM, foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Snarky.Data.EllipticCurve as EC
import Type.Proxy (Proxy(..))

-- | Multi-scalar multiplication with constant bases.
-- |
-- | Given pairs `[{s_i, B_i}]`, computes `sum_i [s_i] * B_i` where each `B_i`
-- | is a constant point and each `s_i` is a circuit variable.
-- |
-- | Internally uses `scaleFast2'` which computes `[s + 2^n] * B` (shifted),
-- | then corrects by subtracting `sum_i [2^n] * B_i` as a constant.
multiscaleKnown
  :: forall @nChunks f n bitsUsed sDiv2Bits t m _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable sDiv2Bits Int
  => Reflectable bitsUsed Int
  => CircuitM f (KimchiConstraint f) t m
  => CurveParams f
  -> NonEmptyArray
       { scalar :: FVar f
       , base :: AffinePoint (F f)
       }
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
multiscaleKnown params pairs = unsafePartial do
  let n = reflectType (Proxy :: Proxy n)
  results <- traverse
    ( \{ scalar, base } -> do
        -- scaleFast2' splits scalar, constrains the split, then computes [scalar + 2^n] * base
        result <- scaleFast2' @nChunks (constPoint base) scalar
        -- Pure: [2^n] * base (shift correction)
        let correction = pow2pow base n
        pure { result, correction }
    )
    pairs
  -- Accumulate circuit results with addComplete
  let { head, tail } = NonEmptyArray.uncons results
  accumulated <- foldM (\acc r -> _.p <$> addComplete acc r.result) head.result tail
  -- Sum pure corrections and negate
  let
    totalCorrection = foldl
      (\acc r -> addPure acc (unwrapF r.correction))
      (unwrapF head.correction)
      tail
  -- Subtract total correction as a constant point
  _.p <$> addComplete accumulated (constPoint $ wrapF $ EC.negate_ totalCorrection)
  where
  constPoint { x: F x, y: F y } = { x: const_ x, y: const_ y }
  unwrapF { x: F x, y: F y } = { x, y }
  wrapF { x, y } = { x: F x, y: F y }

  -- | Pure affine addition that handles the doubling case
  addPure p1 p2
    | p1.x == p2.x && p1.y == p2.y = unwrapF $ EC.double params (wrapF p1)
    | otherwise = unsafePartial $ fromJust $ EC.toAffine $ EC.addAffine p1 p2

  -- | Compute [2^k] * p by iterating pure doubling k times
  pow2pow p k
    | k <= 0 = p
    | otherwise = pow2pow (EC.double params p) (k - 1)
