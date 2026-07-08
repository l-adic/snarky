module Snarky.Circuit.Kimchi.EndoMul
  ( endo
  , endoInv
  , EndoRow
  , computeEndoChain
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (EvaluationError, F(..), FVar, SizedF, Snarky, addConstraint, assertEqual_, const_, exists, label, mkWitnessTable, read, readCVar, scale_, seal, throwAsProver)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoScalar (expandToEndoScalar)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class PrimeField, class WeierstrassCurve, EndoBase(..), endoBase, fromAffine, scalarMul, toAffine)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Data.EllipticCurve.Projective (doubleAddChain)

-- | Per-round witness record of `endo` — exactly what the gadget's exists
-- | body witnesses for one 4-bit round (two double-add steps).
type EndoRow f =
  { r :: AffinePoint f
  , s1 :: f
  , s3 :: f
  , s :: AffinePoint f
  , nAccNext :: f
  , inv :: f
  }

-- | The gadget's entire witness chain via `doubleAddChain` (three field
-- | inversions total instead of four PER ROUND — Montgomery's trick over
-- | a projective walk). Each round is two steps `t' = 2·t + Q` with
-- | `Q1 = ((1 + (endo−1)·b1)·xt, (2·b2−1)·yt)` and `Q2` likewise from
-- | b3/b4; the `nAcc` chain is division-free and computed alongside. The
-- | values are the same field elements the sequential body produced, so
-- | witnesses stay byte-identical.
computeEndoChain
  :: forall f
   . PrimeField f
  => { xt :: f
     , yt :: f
     , eb :: f
     , acc0 :: AffinePoint f
     , bitRounds :: Array { b1 :: f, b2 :: f, b3 :: f, b4 :: f }
     }
  -> Either EvaluationError (Array (EndoRow f))
computeEndoChain { xt, yt, eb, acc0, bitRounds } = do
  let
    dbl v = v + v
    qOf bi bj = AffinePoint { x: (one + (eb - one) * bi) * xt, y: (dbl bj - one) * yt }
    steps = bitRounds >>= \{ b1, b2, b3, b4 } -> [ qOf b1 b2, qOf b3 b4 ]
  rows <- doubleAddChain "endoMul" acc0 steps
  let
    dblN v = v + v
    nAccs = _.out $ foldl
      ( \st { b1, b2, b3, b4 } ->
          let
            n' = dblN (dblN (dblN (dblN st.n + b1) + b2) + b3) + b4
          in
            { n: n', out: Array.snoc st.out n' }
      )
      { n: zero, out: [] }
      bitRounds
    ix arr i = unsafePartial (Array.unsafeIndex arr i)
    AffinePoint a0 = acc0
  pure $ Array.mapWithIndex
    ( \j nAccNext ->
        let
          e = ix rows (2 * j)
          o = ix rows (2 * j + 1)
          xp = if j == 0 then a0.x else (ix rows (2 * j - 1)).xRes
        in
          { r: AffinePoint { x: e.xRes, y: e.yRes }
          , s1: e.s1
          , s3: o.s1
          , s: AffinePoint { x: o.xRes, y: o.yRes }
          , nAccNext
          , inv: recip ((xp - e.xRes) * (e.xRes - o.xRes))
          }
    )
    nAccs

{-
endo satisfies the equation

  endo g a ~ scalarMul (toFieldPure a endoScalar) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS.
-}
endo
  :: forall f f' r n @k @l _l
   . FieldSizeInBits f n
  => HasEndo f f'
  => Reflectable k Int
  => Mul 4 l k
  => Add 1 _l l
  => PrimeField f
  => Compare k n LT
  => AffinePoint (FVar f)
  -> SizedF k (FVar f)
  -> Snarky f (KimchiConstraint f) r
       (AffinePoint (FVar f))
endo g scalar = label "endo" do
  let AffinePoint gr = g
  msbBits <- exists do
    vVal :: SizedF k (F f) <- read scalar
    let lsbBits = SizedF.toBits vVal
    pure $ map (\x -> if x then (one :: F f) else zero) (Vector.reverse lsbBits)
  -- acc = [2] (g + \phi g)
  let
    chunks :: Vector l (Vector 4 (FVar f))
    chunks = Vector.chunks @4 msbBits
    EndoBase (eb :: f) = endoBase @f @f'
  accInit <- do
    -- Seal the endo-scaled x coordinate BEFORE addComplete, matching OCaml's
    -- seal(Field.scale xt Endo.base) which happens outside add_fast.
    phix <- label "seal_endo_x" $ seal (scale_ eb gr.x)
    -- Use addFast CheckFinite matching OCaml's add_fast default (check_finite=true).
    -- This makes inf = Const 0, whose reduce_to_v pairs with the queued seal constraint.
    { p } <- addFast CheckFinite g (AffinePoint (gr { x = phix }))
    _.p <$> addFast CheckFinite p p
  -- The first round's exists body computes the whole batched witness chain
  -- (`computeEndoChain`); the rest index into it. Advice-only: the emitted
  -- circuit is untouched.
  let
    bit4 :: Vector 4 (F f) -> Int -> f
    bit4 vals i = case vals !! unsafeFinite i of F v -> v
  chainAt <- mkWitnessTable "endoMul" do
    AffinePoint t0 <- read @(AffinePoint f) g
    acc0 <- read @(AffinePoint f) accInit
    bitRounds <- traverse
      ( \bs4 -> traverse readCVar bs4 <#> \(vals :: Vector 4 (F f)) ->
          { b1: bit4 vals 0, b2: bit4 vals 1, b3: bit4 vals 2, b4: bit4 vals 3 }
      )
      (Vector.toUnfoldable chunks :: Array (Vector 4 (FVar f)))
    case computeEndoChain { xt: t0.x, yt: t0.y, eb, acc0, bitRounds } of
      Left e -> throwAsProver e
      Right tbl ->
        pure
          ( coerce tbl
              :: Array
                   { r :: AffinePoint f
                   , s1 :: F f
                   , s3 :: F f
                   , s :: AffinePoint f
                   , nAccNext :: F f
                   , inv :: F f
                   }
          )
  Tuple rounds { nAcc, acc } <- mapAccumM
    ( \st bs -> do
        -- OCaml uses !acc and !n_acc directly (not mk/exists) for xp, yp, n_acc_prev.
        -- This preserves variable identity for permutation wiring.
        { r, s1, s3, s, nAccNext, inv } <- exists (chainAt st.idx)
        pure $ Tuple
          { bits: bs, p: st.acc, r, s1, s3, t: g, nAcc: st.nAcc, nAccNext, s, inv }
          { nAcc: nAccNext, acc: s, idx: st.idx + 1 }
    )
    { nAcc: const_ zero, acc: accInit, idx: 0 }
    chunks
  assertEqual_ nAcc (SizedF.toField scalar)
  addConstraint $ KimchiEndoMul { nAcc, s: acc, state: Vector.toUnfoldable1 rounds }
  pure acc

{-
endoInv satisfies the equation

  endoInv g a ~ scalarMul (recip (toFieldPure a endoScalar)) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS.
-}
endoInv
  :: forall @f @f' @g r n
   . FieldSizeInBits f n
  => FieldSizeInBits f' n
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => PrimeField f
  => Compare 128 n LT
  => AffinePoint (FVar f)
  -> SizedF 128 (FVar f)
  -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
endoInv g scalar = label "endo-inv" do
  -- Witness the result: g * (1 / effective_scalar)
  -- Uses WeierstrassAffinePoint so exists triggers assert_on_curve check,
  -- matching OCaml's G.typ which has check = assert_on_curve.
  WeierstrassAffinePoint result :: WeierstrassAffinePoint g _ <- exists do
    -- Read the input point
    AffinePoint { x: gx, y: gy } <- read @(AffinePoint _) g
    -- Read the scalar challenge
    scalarVal :: SizedF 128 (F f) <- read scalar

    -- Compute effective scalar in the scalar field f'
    let
      effectiveScalar :: f'
      effectiveScalar = expandToEndoScalar (coerce scalarVal :: SizedF 128 f)

    -- Compute inverse scalar
    let
      invScalar :: f'
      invScalar = recip effectiveScalar

    -- Convert input point to curve group element and scale by inverse
    let
      gPoint :: g
      gPoint = fromAffine @f @g { x: gx, y: gy }

      resultPoint :: g
      resultPoint = scalarMul invScalar gPoint

    -- Convert result back to AffinePoint
    let { x: rx, y: ry } = unsafePartial $ fromJust $ toAffine @f @g resultPoint
    pure $ WeierstrassAffinePoint { x: F rx, y: F ry }

  -- Verify: endo(result, scalar) == g
  AffinePoint computed <- endo @128 @32 (AffinePoint result) scalar
  let AffinePoint gv = g
  assertEqual_ computed.x gv.x
  assertEqual_ computed.y gv.y
  pure (AffinePoint result)
