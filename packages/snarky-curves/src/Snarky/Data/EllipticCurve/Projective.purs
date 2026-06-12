-- | Out-of-circuit batched curve arithmetic for scalar-mul witness
-- | chains: projective (homogeneous-coordinate) point formulas — which
-- | are division-free — plus Montgomery's batch-inversion trick to
-- | normalize back to affine, paying a few field inversions per CHAIN
-- | instead of per step. ("Montgomery" here names the inversion trick;
-- | the curves are short Weierstrass.)
module Snarky.Data.EllipticCurve.Projective
  ( batchInverse
  , doubleProjective
  , addProjectiveNonEqual
  , DoubleAddRow
  , doubleAddChain
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (EvaluationError(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..), CurveParams, Point(..), fromAffine)

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
