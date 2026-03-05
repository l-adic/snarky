-- | Per-field-width public input commitment.
-- |
-- | Replaces the uniform-width `publicInputCommitment` (which uses a single
-- | @nChunks for all scalars) with a typeclass that walks a structured public
-- | input type and performs scalar multiplications with the optimal bit width
-- | for each leaf:
-- |   - FVar f:              255 bits → 51 chunks
-- |   - SizedF 128 (FVar f): 130 bits → 26 chunks
-- |   - BoolVar f:             5 bits →  1 chunk
-- |
-- | This mirrors OCaml's `Spec.pack` which tags each field element as
-- | `Field` (full width) or `Packed_bits(x, n)` for the MSM.
-- |
-- | Lagrange bases are consumed left-to-right in RowList (alphabetical) order,
-- | matching CircuitType's field ordering for consistent allocation.
module Pickles.PublicInputCommit
  ( class PublicInputCommit
  , class RPublicInputCommit
  , MsmTerm(..)
  , ScalarMulResult
  , scalarMuls
  , rScalarMuls
  , publicInputCommit
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldM, foldl)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Mul)
import Prim.Row as Row
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, addConstraint, const_, if_)
import Snarky.Constraint.Basic (boolean) as Basic
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (SplitField(..), Type1(..), Type2(..))
import Type.Proxy (Proxy(..))

-- | A single term from walking the public input structure.
-- | Matches OCaml's `Add_with_correction` and `Cond_add` variants.
data MsmTerm f
  = AddWithCorrection { point :: AffinePoint (FVar f), correction :: AffinePoint (F f) }
  | CondAdd (BoolVar f) (AffinePoint (F f))

-- | Intermediate result from walking the structure.
type ScalarMulResult f =
  { results :: Array (MsmTerm f)
  , rest :: Array (AffinePoint (F f))
  }

-------------------------------------------------------------------------------
-- | Typeclass
-------------------------------------------------------------------------------

-- | Per-field-width public input commitment.
-- |
-- | Walks a structured public input type, performing scalar multiplications
-- | with optimal bit width per leaf field type.
-- |
-- | Lagrange bases are consumed left-to-right in RowList (alphabetical) order,
-- | matching CircuitType field ordering.
class PublicInputCommit a f where
  scalarMuls
    :: forall t m
     . CircuitM f (KimchiConstraint f) t m
    => CurveParams f
    -> a
    -> Array (AffinePoint (F f))
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)

-------------------------------------------------------------------------------
-- | Leaf instances
-------------------------------------------------------------------------------

-- | Full field element: 255 bits → 51 chunks, sDiv2Bits = 254
instance (FieldSizeInBits f 255) => PublicInputCommit (FVar f) f where
  scalarMuls = scalarMulLeaf @51 @254

-- | 128-bit challenge: 130 bits → 26 chunks, sDiv2Bits = 127
instance (FieldSizeInBits f 255) => PublicInputCommit (SizedF 128 (FVar f)) f where
  scalarMuls params sized bases = scalarMulLeaf @26 @127 params (toField sized) bases

-- | Boolean: Cond_add — conditionally add Lagrange point.
-- | Matches OCaml's `Cond_add(b, lagrange(i))` for 1-bit values.
instance PublicInputCommit (BoolVar f) f where
  scalarMuls _ bool bases =
    let { head, tail } = unsafePartial $ fromJust $ Array.uncons bases
    in pure { results: [ CondAdd bool head ], rest: tail }

-- | Shifted scalar (Type1): single field element, 255 bits → 51 chunks, sDiv2Bits = 254.
instance (FieldSizeInBits f 255) => PublicInputCommit (Type1 (FVar f)) f where
  scalarMuls params (Type1 fv) bases = scalarMulLeaf @51 @254 params fv bases

-- | Shifted scalar (SplitField): sDiv2 (full width, 255 bits → 51 chunks) + sOdd (Cond_add).
-- | sDiv2 = (s - sOdd) / 2 can be up to 254 bits for full-width shifted scalars
-- | (combinedInnerProduct, b, perm, zetaToSrsLength, zetaToDomainSize).
-- | Alphabetical field order (sDiv2 < sOdd) matches CircuitType's Generic instance.
instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (SplitField (FVar f) (BoolVar f)) f where
  scalarMuls params (SplitField { sDiv2, sOdd }) bases = do
    { results: r1, rest: rest1 } <- scalarMulLeaf @51 @254 params sDiv2 bases
    let { head: oddBase, tail: rest2 } = unsafePartial $ fromJust $ Array.uncons rest1
    pure { results: r1 <> [ CondAdd sOdd oddBase ], rest: rest2 }

-- | Type2-wrapped SplitField: delegates to bare SplitField instance.
instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (Type2 (SplitField (FVar f) (BoolVar f))) f where
  scalarMuls params (Type2 sf) bases = scalarMuls params sf bases

-------------------------------------------------------------------------------
-- | Structural instances
-------------------------------------------------------------------------------

-- | Tuple: process first component, then second.
-- | Used for circuit public inputs = (circuitInput, circuitOutput).
instance (PublicInputCommit a f, PublicInputCommit b f) => PublicInputCommit (Tuple a b) f where
  scalarMuls params (Tuple a b) bases = do
    { results: r1, rest: rest1 } <- scalarMuls params a bases
    { results: r2, rest: rest2 } <- scalarMuls params b rest1
    pure { results: r1 <> r2, rest: rest2 }

-- | Unit: contributes no fields.
instance PublicInputCommit Unit f where
  scalarMuls _ _ bases = pure { results: [], rest: bases }

-- | Vector: process each element sequentially
instance
  ( PublicInputCommit a f
  , Reflectable n Int
  ) =>
  PublicInputCommit (Vector n a) f where
  scalarMuls params vec bases =
    foldM
      ( \acc elem -> do
          { results, rest } <- scalarMuls params elem acc.rest
          pure { results: acc.results <> results, rest }
      )
      { results: [], rest: bases }
      vec

-- | Record: via RowList (alphabetical field order)
instance
  ( RL.RowToList r rl
  , RPublicInputCommit rl f r
  ) =>
  PublicInputCommit (Record r) f where
  scalarMuls params rec bases = rScalarMuls @rl params rec bases

-------------------------------------------------------------------------------
-- | RowList walker
-------------------------------------------------------------------------------

class RPublicInputCommit (rl :: RL.RowList Type) f (r :: Row Type) | rl -> r where
  rScalarMuls
    :: forall t m
     . CircuitM f (KimchiConstraint f) t m
    => CurveParams f
    -> Record r
    -> Array (AffinePoint (F f))
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)

instance RPublicInputCommit RL.Nil f () where
  rScalarMuls _ _ bases = pure { results: [], rest: bases }

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , PublicInputCommit a f
  , RPublicInputCommit tail f rest
  ) =>
  RPublicInputCommit (RL.Cons s a tail) f r where
  rScalarMuls params rec bases = do
    let field = Record.get (Proxy @s) rec
    { results: r1, rest: rest1 } <- scalarMuls params field bases
    { results: r2, rest: rest2 } <- rScalarMuls @tail params (Record.delete (Proxy @s) rec) rest1
    pure { results: r1 <> r2, rest: rest2 }

-------------------------------------------------------------------------------
-- | Top-level commitment function
-------------------------------------------------------------------------------

-- | Compute public input commitment from a structured input type.
-- |
-- | Walks the input via PublicInputCommit, performing per-field scalar
-- | multiplications with optimal bit widths, then combines:
-- |   xHat = -(MSM result) + blindingH
-- |
-- | where MSM = sum([s_i] * B_i) after shift correction.
publicInputCommit
  :: forall a f t m r
   . PublicInputCommit a f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => { curveParams :: CurveParams f
     , lagrangeComms :: Array (AffinePoint (F f))
     , blindingH :: AffinePoint (F f)
     | r
     }
  -> a
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
publicInputCommit params input = do
  { results } <- scalarMuls params.curveParams input params.lagrangeComms
  case NEA.fromArray results of
    Nothing -> pure (constPt params.blindingH)
    Just results' -> unsafePartial do
      -- Separate scalar mul terms (with corrections) from cond_add terms
      let
        correctionPts = Array.mapMaybe
          ( case _ of
              AddWithCorrection r -> Just (constPt r.correction)
              CondAdd _ _ -> Nothing
          )
          (NEA.toArray results')

      -- 1. Sum corrections in-circuit: init accumulator = sum([2^n] * B_i)
      --    Matches OCaml: correction = reduce corrections ~f:add_fast
      --    NOTE: These are all constant points so this could be done as pure math,
      --    but OCaml generates CompleteAdd gates here and we match for equivalence.
      let { head: corrHead, tail: corrTail } = fromJust $ Array.uncons correctionPts
      init <- foldM (\acc c -> _.p <$> addComplete acc c) corrHead corrTail

      -- 2. Fold over all terms, matching OCaml's fold order:
      --    - AddWithCorrection: acc = add_fast(acc, scale_fast2'(...))
      --    - CondAdd: acc = if_ b then add_fast(lagrange, acc) else acc
      acc <- foldM
        ( \acc term -> case term of
            AddWithCorrection { point } -> _.p <$> addComplete acc point
            CondAdd b lagrangePt -> do
              addConstraint (Basic.boolean (coerce b :: FVar f))
              added <- _.p <$> addComplete (constPt lagrangePt) acc
              x' <- if_ b added.x acc.x
              y' <- if_ b added.y acc.y
              pure { x: x', y: y' }
        )
        init
        (NEA.toArray results')

      -- 3. Negate and add blinding generator
      negAcc <- Curves.negate acc
      _.p <$> addComplete negAcc (constPt params.blindingH)

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

-- | Single scalar mul with shift correction.
-- | Consumes one Lagrange base from the array.
-- |
-- | Uses @nChunks to control the bit width: bitsUsed = 5 * nChunks.
-- | The correction is [2^bitsUsed] * base, matching OCaml's
-- | `lagrange_with_correction ~input_length`.
scalarMulLeaf
  :: forall @nChunks @sDiv2Bits f n bitsUsed _l _afterBits t m
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits _afterBits n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => CurveParams f
  -> FVar f
  -> Array (AffinePoint (F f))
  -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)
scalarMulLeaf params scalar bases = do
  let { head, tail } = unsafePartial $ fromJust $ Array.uncons bases
  point <- scaleFast2' @nChunks @sDiv2Bits (constPt head) scalar
  let actualShift = reflectType (Proxy @bitsUsed)
  -- Correction is negated to match OCaml: correction = negate([2^shift] * base)
  -- so that init = Σ(correction_i) + Σ(scaleFast2'(g_i, s_i)) = Σ([s_i] * g_i)
  let correction = wrapPt $ EC.negate_ $ unwrapPt $ pow2pow params head actualShift
  pure
    { results: [ AddWithCorrection { point, correction } ]
    , rest: tail
    }

constPt :: forall f. PrimeField f => AffinePoint (F f) -> AffinePoint (FVar f)
constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }

unwrapPt :: forall f. AffinePoint (F f) -> AffinePoint f
unwrapPt { x: F x', y: F y' } = { x: x', y: y' }

wrapPt :: forall f. AffinePoint f -> AffinePoint (F f)
wrapPt { x, y } = { x: F x, y: F y }

-- | Pure affine addition of AffinePoint (F f) values.
addPurePts :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> AffinePoint (F f) -> AffinePoint (F f)
addPurePts params p1 p2
  | unwrapPt p1 == unwrapPt p2 = EC.double params p1
  | otherwise =
      let
        { x, y } = unsafePartial $ fromJust $ EC.toAffine $ EC.addAffine (unwrapPt p1) (unwrapPt p2)
      in
        { x: F x, y: F y }

-- | Compute [2^k] * p by iterating pure doubling.
pow2pow :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> Int -> AffinePoint (F f)
pow2pow _ p k
  | k <= 0 = p
pow2pow params p k = pow2pow params (EC.double params p) (k - 1)
