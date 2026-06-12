-- | Shifted-accumulator scalar multiplication — direct port of
-- | `Snarky_curves.Make_weierstrass_checked.{Shifted, scale}`
-- | (`mina/src/lib/crypto/snarky_curves/snarky_curves.ml`).
-- |
-- | Production `Snark_params.Tick.Inner_curve.Checked` instantiates
-- | `Make_weierstrass_checked` with the `Override.add =
-- | Some Pickles.Step_main_inputs.Ops.add_fast` argument
-- | (`snark_params.ml:196-201`), so every `add_exn` inside the
-- | functor — including `Shifted.add` and `Shifted.unshift_nonzero` —
-- | resolves to the kimchi CompleteAdd gate, not the chord-and-tangent
-- | generic add. `double` is NOT overridden, so it stays the generic
-- | chord (4 constraints).
-- |
-- | Mirrors that exactly:
-- |   * `add` and `unshiftNonzero` → kimchi `addFast` (CompleteAdd)
-- |   * `double`  → `Snarky.Circuit.Curves.double` (generic chord)
-- |   * `if_`     → record IfThenElse (point-wise field if)
-- |
-- | The shift is `exists`-allocated; its witness is supplied as a
-- | caller-provided constant (OCaml uses `Curve.random ()`; witness
-- | value doesn't enter the constraint system either way).
module Snarky.Circuit.Schnorr.Shifted
  ( Shifted
  , ShiftedOps
  , assertOnCurveConst
  , createShifted
  , pallasScalarOps
  , vestaScalarOps
  , scale
  , scaleKnown
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.List as List
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.Curves (double, negate) as Curves
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, Snarky, and_, assertSquare_, const_, exists, if_, mul_, square_)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Types (Bool(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Class (class WeierstrassCurve, curveParams, fromAffine, generator, toAffine) as C
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), CurveParams)
import Type.Proxy (Proxy(..))

-- | Shifted accumulator. The wrapped point is `shift + (partial
-- | sum)`; the actual sum is recovered via `unshiftNonzero`.
newtype Shifted f = Shifted (AffinePoint (FVar f))

-- | Ops parameterised by a single shift (allocated by `createShifted`).
type ShiftedOps f r =
  { zero :: Shifted f
  , add ::
      Shifted f
      -> AffinePoint (FVar f)
      -> Snarky f (KimchiConstraint f) r (Shifted f)
  , if_ ::
      BoolVar f
      -> Shifted f
      -> Shifted f
      -> Snarky f (KimchiConstraint f) r (Shifted f)
  , unshiftNonzero ::
      Shifted f
      -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
  }

-- | Pallas-style `assert_on_curve` matching OCaml
-- | `Snarky_curves.Make_weierstrass_checked.assert_on_curve`
-- | (`snarky_curves.ml:154-159`):
-- |
-- |   let x2 = square x          -- Square
-- |   let x3 = x2 * x            -- R1CS
-- |   let ax = constant a * x    -- no constraint (const * var)
-- |   assert_square y (x3 + ax + constant b)   -- Square
-- |
-- | 3 constraints in the exact order Square, R1CS, Square.
-- | Curve params are constants (not field vars); `a*x` is folded
-- | symbolically via `CVar.scale_`.
assertOnCurveConst
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => CurveParams f
  -> AffinePoint (FVar f)
  -> Snarky f c r Unit
assertOnCurveConst { a, b } (AffinePoint { x, y }) = do
  x2 <- square_ x
  x3 <- mul_ x2 x
  let
    ax = CVar.scale_ a x
    rhs = CVar.add_ x3 (CVar.add_ ax (const_ b))
  assertSquare_ y rhs

-- | `exists`-allocate a fresh shift, run assert_on_curve on it (so
-- | the constraint count includes the typ check production gets
-- | "for free" via `Inner_curve.typ`'s check), and return ops.
-- | Mirrors `Inner_curve.Checked.Shifted.create ()`.
createShifted
  :: forall f r
   . PrimeField f
  => CurveParams f
  -> AffinePoint f
  -> Snarky f (KimchiConstraint f) r (ShiftedOps f r)
createShifted curveParams shiftConst = do
  shift <- exists $ pure shiftConst
  assertOnCurveConst curveParams shift
  let
    zero :: Shifted f
    zero = Shifted shift

    -- `CheckFinite` matches OCaml `Pickles.Step_main_inputs.Ops.add_fast`'s
    -- default (`?(check_finite = true)`) — `inf` is the constant
    -- `Field.zero`, which materialises into a fresh variable + 1 Generic
    -- assertion (`v = 0`) per add_fast call. `DontCheckFinite` would
    -- save that constraint but produce a different gate shape than
    -- production.
    add (Shifted acc) pt = do
      { p } <- addFast CheckFinite acc pt
      pure (Shifted p)

    -- OCaml `Shifted.if_` (snarky_curves.ml:233-236) evaluates x's
    -- F.if_ BEFORE y's via `let%map x = F.if_ ... and y = F.if_ ...`.
    -- PS's record IfThenElse processes fields in reverse (snd first)
    -- for general OCaml compatibility, so we inline the x-then-y
    -- order here to keep wires aligned with production.
    ifS b (Shifted (AffinePoint t1)) (Shifted (AffinePoint t2)) = do
      x <- if_ @f b t1.x t2.x
      y <- if_ @f b t1.y t2.y
      pure (Shifted (AffinePoint { x, y }))

    -- OCaml `unshift_nonzero shifted = add_exn (negate shift) shifted`
    -- — negShift is FIRST arg, shifted SECOND. add_exn → add_fast under
    -- production's Override.
    unshiftNonzero (Shifted acc) = do
      negShift <- Curves.negate shift
      { p } <- addFast CheckFinite negShift acc
      pure p
  pure { zero, add, if_: ifS, unshiftNonzero }

-- | A constant on-curve, non-identity shift point (2·G) for the given
-- | curve — its witness value never enters the constraint system, so any
-- | fixed point works; `2·G` is a convenient choice.
shiftFor
  :: forall f g
   . C.WeierstrassCurve f g
  => Semigroup g
  => g
  -> AffinePoint f
shiftFor g = AffinePoint (unsafePartial fromJust $ C.toAffine (g <> g))

-- | Ready-to-use shifted scalar-mul ops for the Pallas curve (point
-- | coordinates in `Pallas.BaseField`), with the curve params and a
-- | standard shift baked in.
pallasScalarOps
  :: forall r
   . PrimeField Pallas.BaseField
  => Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) r (ShiftedOps Pallas.BaseField r)
pallasScalarOps =
  createShifted (C.curveParams (Proxy :: Proxy PallasG)) (shiftFor (C.generator :: PallasG))

-- | Ready-to-use shifted scalar-mul ops for the Vesta curve (point
-- | coordinates in `Vesta.BaseField`).
vestaScalarOps
  :: forall r
   . PrimeField Vesta.BaseField
  => Snarky Vesta.BaseField (KimchiConstraint Vesta.BaseField) r (ShiftedOps Vesta.BaseField r)
vestaScalarOps =
  createShifted (C.curveParams (Proxy :: Proxy VestaG)) (shiftFor (C.generator :: VestaG))

-- | LSB-first unbounded double-and-add. Direct port of
-- | `Snarky_curves.Make_weierstrass_checked.scale`
-- | (`snarky_curves.ml:326-345`):
-- |
-- | @
-- | scale (module Shifted) t bits ~init:acc =
-- |   for each b_i (LSB-first):
-- |     add_pt = Shifted.add acc pt    (kimchi CompleteAdd via Override)
-- |     acc'   = Shifted.if_ b_i ~then_:add_pt ~else_:acc
-- |     pt'    = double pt              (generic chord, 4 constraints)
-- |   return acc
-- | @
scale
  :: forall f r n
   . PrimeField f
  => CurveParams f
  -> ShiftedOps f r
  -> Shifted f
  -> AffinePoint (FVar f)
  -> Vector n (BoolVar f)
  -> Snarky f (KimchiConstraint f) r (Shifted f)
scale params ops init base bits = do
  Tuple acc _ <- foldM step (Tuple init base)
    (Vector.toUnfoldable bits :: Array _)
  pure acc
  where
  step (Tuple acc pt) b = do
    addPt <- ops.add acc pt
    acc' <- ops.if_ b addPt acc
    pt' <- Curves.double params pt
    pure $ Tuple acc' pt'

-- | `lookup_point (b0, b1) (t1, t2, t3, t4)` — 2-bit table lookup over
-- | 4 constant curve points. Returns
-- |   `t1 + b0*(t2 - t1) + b1*(t3 - t1) + (b0 ∧ b1)*(t4 + t1 - t2 - t3)`
-- | as a symbolic CVar pair (no constraint other than the `b0 ∧ b1`
-- | boolean AND). Mirrors `Snarky_curves.lookup_point`
-- | (`snarky_curves.ml:351-366`).
lookupPoint
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => Tuple (BoolVar f) (BoolVar f)
  -> { t1 :: AffinePoint f
     , t2 :: AffinePoint f
     , t3 :: AffinePoint f
     , t4 :: AffinePoint f
     }
  -> Snarky f c r (AffinePoint (FVar f))
lookupPoint (Tuple b0 b1) { t1: AffinePoint t1, t2: AffinePoint t2, t3: AffinePoint t3, t4: AffinePoint t4 } = do
  b0AndB1 <- and_ b0 b1
  let
    lookupOne a1 a2 a3 a4 =
      CVar.add_ (const_ a1)
        ( CVar.add_ (CVar.scale_ (a2 - a1) (coerce b0 :: FVar f))
            ( CVar.add_ (CVar.scale_ (a3 - a1) (coerce b1 :: FVar f))
                (CVar.scale_ (a4 + a1 - a2 - a3) (coerce b0AndB1 :: FVar f))
            )
        )
  pure $ AffinePoint
    { x: lookupOne t1.x t2.x t3.x t4.x
    , y: lookupOne t1.y t2.y t3.y t4.y
    }

-- | `lookup_single_bit b (t1, t2)` — 1-bit table lookup over 2
-- | constant points: `t1 + b * (t2 - t1)`. No constraint.
-- | Mirrors `Snarky_curves.lookup_single_bit`
-- | (`snarky_curves.ml:369-376`).
lookupSingleBit
  :: forall f
   . PrimeField f
  => BoolVar f
  -> { t1 :: AffinePoint f, t2 :: AffinePoint f }
  -> AffinePoint (FVar f)
lookupSingleBit b { t1: AffinePoint t1, t2: AffinePoint t2 } =
  let
    lookupOne a1 a2 =
      CVar.add_ (const_ a1) (CVar.scale_ (a2 - a1) (coerce b :: FVar f))
  in
    AffinePoint { x: lookupOne t1.x t2.x, y: lookupOne t1.y t2.y }

-- | Fixed-base scalar multiplication for a constant point `t`.
-- | Direct port of `Snarky_curves.Make_weierstrass_checked.scale_known`
-- | (`snarky_curves.ml:378-458`):
-- |
-- |   sigma         = t   (acts as the "shift" sum-correction base)
-- |   sigma_count   = (n + 1) / 2
-- |   to_term i (b0, b1) = sigma + b0*2^i*t + b1*2^(i+1)*t
-- |   sum = Σ to_term(2j) (b_{2j}, b_{2j+1})   (j = 0..n/2-1)
-- |       = sigma_count*sigma + b*t            where b = Σ b_i*2^i
-- |   result = sum - sigma_count*sigma = b*t   (final unshift)
-- |
-- | For odd n the last bit folds in via `lookup_single_bit`.
-- |
-- | Roughly 2× fewer kimchi-CompleteAdd gates than plain `scale` for
-- | the same bit-length, at the cost of one boolean AND per
-- | 2-bit window.
scaleKnown
  :: forall f g r n
   . PrimeField f
  => C.WeierstrassCurve f g
  => Semigroup g
  => ShiftedOps f r
  -> g
  -> Vector n (BoolVar f)
  -> Shifted f
  -> Snarky f (KimchiConstraint f) r (Shifted f)
scaleKnown ops t bits init = do
  let
    sigma :: AffinePoint f
    sigma = AffinePoint (unsafePartial fromJust $ C.toAffine t)
    -- LSB-first bit list
    bs = List.fromFoldable (Vector.toUnfoldable bits :: Array (BoolVar f))
    n = List.length bs
    sigmaCount = (n + 1) / 2

    -- Precompute the 4-entry tables for each 2-bit window.
    toTermPoints :: g -> g -> _
    toTermPoints twoToI twoToIPlus1 =
      let
        s = t
        sPlusI = s <> twoToI
        sPlusIp1 = s <> twoToIPlus1
        sPlusBoth = s <> twoToI <> twoToIPlus1
        affine p = AffinePoint (unsafePartial fromJust (C.toAffine p))
      in
        { t1: affine s, t2: affine sPlusI, t3: affine sPlusIp1, t4: affine sPlusBoth }
    go acc twoToI = case _ of
      List.Nil -> pure acc
      List.Cons bi List.Nil -> do
        let term = lookupSingleBit bi { t1: sigma, t2: AffinePoint (unsafePartial fromJust (C.toAffine (t <> twoToI))) }
        ops.add acc term
      List.Cons bi (List.Cons biPlus1 rest) -> do
        let
          twoToIPlus1 = twoToI <> twoToI
          tbl = toTermPoints twoToI twoToIPlus1
        term <- lookupPoint (Tuple bi biPlus1) tbl
        acc' <- ops.add acc term
        go acc' (twoToIPlus1 <> twoToIPlus1) rest
  resultWithShift <- go init t bs
  -- Final unshift: subtract sigma_count * sigma.
  -- Compute -(sigma_count * sigma) = sigma_count * (-sigma) where (-)
  -- on an affine Weierstrass point just flips the y coordinate.
  let
    negSigmaPt :: g
    negSigmaPt =
      let
        AffinePoint s = sigma
      in
        C.fromAffine { x: s.x, y: zero - s.y }

    unshiftPt :: g
    unshiftPt = intScale sigmaCount negSigmaPt
    unshiftAffine = unsafePartial fromJust (C.toAffine unshiftPt)

    unshiftConstVar :: AffinePoint (FVar f)
    unshiftConstVar = AffinePoint { x: const_ unshiftAffine.x, y: const_ unshiftAffine.y }
  ops.add resultWithShift unshiftConstVar

-- | Naive Int-scaled group operation via double-and-add. Works for any
-- | Semigroup; for n=0 returns the argument doubled to itself (which is
-- | wrong for n=0 but n>0 is guaranteed by callers here).
intScale :: forall g. Semigroup g => Int -> g -> g
intScale n g
  | n <= 1 = g
  | n `mod` 2 == 1 = g <> intScale (n - 1) g
  | otherwise = let half = intScale (n / 2) g in half <> half

