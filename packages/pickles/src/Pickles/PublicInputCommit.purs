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
-- | Lagrange bases are fetched by index left-to-right in RowList (alphabetical)
-- | order, matching CircuitType's field ordering. The walk threads an `Int`
-- | counter through each instance and calls a user-supplied
-- | `LagrangeBaseLookup` closure whenever it needs a new base — the same
-- | shape as OCaml `step_verifier.ml`'s `lagrange_commitment srs i`, so
-- | there is no pre-sized array to get wrong.
module Pickles.PublicInputCommit
  ( class PublicInputCommit
  , class RPublicInputCommit
  , class PackStatement
  , class RPackStatement
  , PackedField
  , CorrectionMode(..)
  , DeferredScaleMul(..)
  , MsmTerm(..)
  , ScalarMulResult
  , packFields
  , rPackFields
  , scalarMuls
  , rScalarMuls
  , publicInputCommit
  , LagrangeBase
  , LagrangeBaseLookup
  , mkConstLagrangeBase
  , mkConstLagrangeBaseLookup
  , wrapPt
  , unwrapPt
  , pow2pow
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..), fromLeft)
import Data.Foldable (foldM, foldl)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Effect.Exception.Unsafe (unsafeThrow)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Mul)
import Prim.Row as Row
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, addConstraint, const_, if_, label)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Constraint.Basic (boolean) as Basic
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (SplitField(..), Type1(..), Type2(..))
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | PackedField: decoupled packing (mirrors OCaml's Spec.pack output)
-------------------------------------------------------------------------------

-- | A tagged field element from packing a structured public input.
-- | Mirrors OCaml's `[ \`Field of f | \`Packed_bits of f * int ]`.
data PackedField f
  = FullField (FVar f) -- ^ Full 255-bit field element (OCaml: \`Field x)
  | PackedBits (FVar f) Int -- ^ n-bit packed value (OCaml: \`Packed_bits(x, n))
  | SplitShifted (FVar f) (BoolVar f) -- ^ Type2 shifted: sDiv2 (255-bit) + sOdd (1-bit)

-- | Walks a structured public input type and produces a flat array of
-- | PackedField values, mirroring OCaml's Spec.pack.
-- | This is the packing step only — no constraints, no MSM.
class PackStatement a f where
  packFields :: a -> Array (PackedField f)

-- Leaf instances
instance PackStatement (FVar f) f where
  packFields fv = [ FullField fv ]

instance PackStatement (SizedF 128 (FVar f)) f where
  packFields sized = [ PackedBits (toField sized) 128 ]

instance PackStatement (SizedF 10 (FVar f)) f where
  packFields sized = [ PackedBits (toField sized) 10 ]

instance PackStatement (BoolVar f) f where
  packFields b = [ PackedBits (coerce b) 1 ]

instance PackStatement (Type1 (FVar f)) f where
  packFields (Type1 fv) = [ FullField fv ]

instance PackStatement (SplitField (FVar f) (BoolVar f)) f where
  packFields (SplitField { sDiv2, sOdd }) = [ SplitShifted sDiv2 sOdd ]

instance PackStatement (Type2 (SplitField (FVar f) (BoolVar f))) f where
  packFields (Type2 sf) = packFields sf

-- Structural instances
instance PackStatement Unit f where
  packFields _ = []

instance (PackStatement a f, PackStatement b f) => PackStatement (Tuple a b) f where
  packFields (Tuple a b) = packFields a <> packFields b

instance (PackStatement a f, Reflectable n Int) => PackStatement (Vector n a) f where
  packFields vec = Array.concatMap packFields (Array.fromFoldable vec)

instance (RL.RowToList r rl, RPackStatement rl f r) => PackStatement (Record r) f where
  packFields rec = rPackFields @rl rec

-- | RowList walker for PackStatement (alphabetical field order)
class RPackStatement (rl :: RL.RowList Type) f (r :: Row Type) | rl -> r where
  rPackFields :: Record r -> Array (PackedField f)

instance RPackStatement RL.Nil f () where
  rPackFields _ = []

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , PackStatement a f
  , RPackStatement tail f rest
  ) =>
  RPackStatement (RL.Cons s a tail) f r where
  rPackFields rec =
    let
      field = Record.get (Proxy @s) rec
    in
      packFields field <> rPackFields @tail (Record.delete (Proxy @s) rec)

-------------------------------------------------------------------------------
-- | PublicInputCommit (existing, now derivable from PackStatement)
-------------------------------------------------------------------------------

-- | Controls how correction points are combined during public input commitment.
-- | PureCorrections: sum as pure field arithmetic (no circuit cost) — for Step verifier.
-- | InCircuitCorrections: sum via in-circuit addComplete gates — for Wrap verifier.
data CorrectionMode = PureCorrections | InCircuitCorrections

-- | A deferred scalar multiplication that captures type-level parameters.
-- | This lets scalarMulLeaf store the computation without executing it,
-- | so publicInputCommit can interleave scale_fast2' and add_fast inline
-- | during the fold (matching OCaml's step_verifier.ml:468-475).
newtype DeferredScaleMul f = DeferredScaleMul
  ( forall t m
     . CircuitM f (KimchiConstraint f) t m
    => Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  )

-- | A single term from walking the public input structure.
-- | Matches OCaml's `Add_with_correction` and `Cond_add` variants.
-- |
-- | Two correction shapes:
-- |
-- |   * `AddWithCorrection` — correction is a compile-time constant,
-- |     produced when `LagrangeBase.correctionAt` is `Nothing`. Used in
-- |     the single-branch / all-domains-equal case (step verifier's
-- |     `PureCorrections` and wrap verifier's degenerate single-branch
-- |     `InCircuitCorrections`). Mirrors OCaml's
-- |     `lagrange_with_correction` fast path
-- |     (wrap_verifier.ml:426-428 — "all domains equal").
-- |
-- |   * `AddWithCircuitCorrection` — correction is an in-circuit FVar
-- |     point (already 1-hot summed across branches). Produced when
-- |     `LagrangeBase.correctionAt` is `Just`. Used by the wrap
-- |     verifier when branch domains differ. Mirrors OCaml's
-- |     `lagrange_with_correction` per-branch path
-- |     (wrap_verifier.ml:429-443).
-- |
-- | CondAdd's Lagrange point is masked (OCaml's `lagrange` always masks).
data MsmTerm f
  = AddWithCorrection { scaleMul :: DeferredScaleMul f, correction :: AffinePoint (F f) }
  | AddWithCircuitCorrection { scaleMul :: DeferredScaleMul f, correction :: AffinePoint (FVar f) }
  | CondAdd (BoolVar f) (AffinePoint (FVar f))

-- | A Lagrange base point.
-- |
-- |   * `constant` — the compile-time constant lagrange point at this
-- |     index. Used by `PureCorrections` mode (step verifier) and by
-- |     `scalarMulLeaf` when computing the compile-time correction
-- |     (single-branch / all-domains-equal fast path).
-- |   * `circuit` — the in-circuit version of the lagrange point.
-- |     For single-branch, this is `constPt constant`. For multi-branch
-- |     with differing domains, this is the 1-hot-summed circuit point
-- |     `sum_b which_branch[b] * lagrange(domain[b], i)`.
-- |   * `correctionAt` — `Nothing` for single-branch / all-equal-domain
-- |     path (caller computes correction from `constant` via `pow2pow`).
-- |     `Just f` for the per-branch path: `f shift` returns the in-circuit
-- |     correction `-sum_b which_branch[b] * [2^shift] * lagrange(domain[b], i)`.
-- |     Set by `mkPerBranchLagrangeBase`; mirrors OCaml's per-branch
-- |     `lagrange_with_correction`.
type LagrangeBase f =
  { constant :: AffinePoint (F f)
  , circuit :: AffinePoint (FVar f)
  , correctionAt :: Maybe (Int -> AffinePoint (FVar f))
  }

-- | Index-based lookup over lagrange bases, mirroring OCaml
-- | `step_verifier.ml`'s `lagrange_commitment srs i` closure. The walk
-- | in `publicInputCommit` fetches bases on demand by index instead of
-- | consuming a pre-sized array, which removes the need for a "numPublic"
-- | parameter at call sites.
type LagrangeBaseLookup f = Int -> LagrangeBase f

-- | Construct a LagrangeBase where both constant and circuit are the same
-- | value. Used in single-branch / all-domains-equal contexts where there's
-- | no per-branch dispatch needed.
mkConstLagrangeBase :: forall f. PrimeField f => AffinePoint (F f) -> LagrangeBase f
mkConstLagrangeBase pt = { constant: pt, circuit: constPt pt, correctionAt: Nothing }

-- | Build a lookup closure from a function returning the constant `i`-th
-- | lagrange commitment. The most common shape at call sites: wrap an FFI
-- | `*SrsLagrangeCommitmentAt srs domainLog2` partial application.
mkConstLagrangeBaseLookup
  :: forall f
   . PrimeField f
  => (Int -> AffinePoint (F f))
  -> LagrangeBaseLookup f
mkConstLagrangeBaseLookup f i = mkConstLagrangeBase (f i)

-- | Intermediate result from walking the structure. The `nextIdx` field is
-- | the first lagrange-base index the caller has *not yet* consumed.
type ScalarMulResult f =
  { results :: Array (MsmTerm f)
  , nextIdx :: Int
  }

-------------------------------------------------------------------------------
-- | Typeclass
-------------------------------------------------------------------------------

-- | Per-field-width public input commitment.
-- |
-- | Walks a structured public input type, performing scalar multiplications
-- | with optimal bit width per leaf field type. Each leaf fetches the base
-- | it needs by calling `lookup idx`, where `idx` is the current walk
-- | position (threaded through the instances).
class PublicInputCommit a f where
  scalarMuls
    :: forall t m
     . CircuitM f (KimchiConstraint f) t m
    => CurveParams f
    -> a
    -> LagrangeBaseLookup f
    -> Int
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)

-------------------------------------------------------------------------------
-- | Leaf instances
-------------------------------------------------------------------------------

-- | Full field element: 255 bits → 51 chunks, sDiv2Bits = 254
instance (FieldSizeInBits f 255) => PublicInputCommit (FVar f) f where
  scalarMuls params scalar lookup idx = scalarMulLeaf @51 @254 params scalar lookup idx

-- | 128-bit challenge: 130 bits → 26 chunks, sDiv2Bits = 127
instance (FieldSizeInBits f 255) => PublicInputCommit (SizedF 128 (FVar f)) f where
  scalarMuls params sized lookup idx = scalarMulLeaf @26 @127 params (toField sized) lookup idx

-- | 10-bit branch data: 10 bits → 2 chunks, sDiv2Bits = 9
instance (FieldSizeInBits f 255) => PublicInputCommit (SizedF 10 (FVar f)) f where
  scalarMuls params sized lookup idx = scalarMulLeaf @2 @9 params (toField sized) lookup idx

-- | Boolean: Cond_add — conditionally add Lagrange point.
-- | Matches OCaml's `Cond_add(b, lagrange(i))` for 1-bit values.
-- | The boolean constraint is generated here (during scalarMuls walk),
-- | matching OCaml which calls assert_(Constraint.boolean b) during
-- | List.map terms construction, BEFORE correction sum and fold.
instance PublicInputCommit (BoolVar f) f where
  scalarMuls _ bool lookup idx = do
    addConstraint (Basic.boolean (coerce bool :: FVar f))
    let base = lookup idx
    pure { results: [ CondAdd bool base.circuit ], nextIdx: idx + 1 }

-- | Shifted scalar (Type1): single field element, 255 bits → 51 chunks, sDiv2Bits = 254.
instance (FieldSizeInBits f 255) => PublicInputCommit (Type1 (FVar f)) f where
  scalarMuls params (Type1 fv) lookup idx = scalarMulLeaf @51 @254 params fv lookup idx

-- | Shifted scalar (SplitField): sDiv2 (full width, 255 bits → 51 chunks) + sOdd (Cond_add).
-- | sDiv2 = (s - sOdd) / 2 can be up to 254 bits for full-width shifted scalars
-- | (combinedInnerProduct, b, perm, zetaToSrsLength, zetaToDomainSize).
-- | Alphabetical field order (sDiv2 < sOdd) matches CircuitType's Generic instance.
instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (SplitField (FVar f) (BoolVar f)) f where
  scalarMuls params (SplitField { sDiv2, sOdd }) lookup idx = do
    { results: r1, nextIdx: idx1 } <- scalarMulLeaf @51 @254 params sDiv2 lookup idx
    addConstraint (Basic.boolean (coerce sOdd :: FVar f))
    let oddBase = lookup idx1
    pure
      { results: r1 <> [ CondAdd sOdd oddBase.circuit ]
      , nextIdx: idx1 + 1
      }

-- | Type2-wrapped SplitField: delegates to bare SplitField instance.
instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (Type2 (SplitField (FVar f) (BoolVar f))) f where
  scalarMuls params (Type2 sf) lookup idx = scalarMuls params sf lookup idx

-------------------------------------------------------------------------------
-- | Structural instances
-------------------------------------------------------------------------------

-- | Tuple: process first component, then second.
-- | Used for circuit public inputs = (circuitInput, circuitOutput).
instance (PublicInputCommit a f, PublicInputCommit b f) => PublicInputCommit (Tuple a b) f where
  scalarMuls params (Tuple a b) lookup idx = do
    { results: r1, nextIdx: idx1 } <- scalarMuls params a lookup idx
    { results: r2, nextIdx: idx2 } <- scalarMuls params b lookup idx1
    pure { results: r1 <> r2, nextIdx: idx2 }

-- | Unit: contributes no fields.
instance PublicInputCommit Unit f where
  scalarMuls _ _ _ idx = pure { results: [], nextIdx: idx }

-- | Vector: process each element sequentially
instance
  ( PublicInputCommit a f
  , Reflectable n Int
  ) =>
  PublicInputCommit (Vector n a) f where
  scalarMuls params vec lookup idx =
    foldM
      ( \acc elem -> do
          { results, nextIdx } <- scalarMuls params elem lookup acc.nextIdx
          pure { results: acc.results <> results, nextIdx }
      )
      { results: [], nextIdx: idx }
      vec

-- | Record: via RowList (alphabetical field order)
instance
  ( RL.RowToList r rl
  , RPublicInputCommit rl f r
  ) =>
  PublicInputCommit (Record r) f where
  scalarMuls params rec lookup idx = rScalarMuls @rl params rec lookup idx

-------------------------------------------------------------------------------
-- | RowList walker
-------------------------------------------------------------------------------

class RPublicInputCommit (rl :: RL.RowList Type) f (r :: Row Type) | rl -> r where
  rScalarMuls
    :: forall t m
     . CircuitM f (KimchiConstraint f) t m
    => CurveParams f
    -> Record r
    -> LagrangeBaseLookup f
    -> Int
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)

instance RPublicInputCommit RL.Nil f () where
  rScalarMuls _ _ _ idx = pure { results: [], nextIdx: idx }

instance
  ( IsSymbol s
  , Row.Cons s a rest r
  , Row.Lacks s rest
  , PublicInputCommit a f
  , RPublicInputCommit tail f rest
  ) =>
  RPublicInputCommit (RL.Cons s a tail) f r where
  rScalarMuls params rec lookup idx = do
    let field = Record.get (Proxy @s) rec
    { results: r1, nextIdx: idx1 } <- scalarMuls params field lookup idx
    { results: r2, nextIdx: idx2 } <- rScalarMuls @tail params (Record.delete (Proxy @s) rec) lookup idx1
    pure { results: r1 <> r2, nextIdx: idx2 }

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
     , lagrangeAt :: LagrangeBaseLookup f
     , blindingH :: AffinePoint (F f)
     , correctionMode :: CorrectionMode
     | r
     }
  -> a
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
publicInputCommit params input = label "public-input-commit" do
  { results } <- scalarMuls params.curveParams input params.lagrangeAt 0
  case NEA.fromArray results of
    Nothing -> pure (constPt params.blindingH)
    Just results' -> unsafePartial do
      case params.correctionMode of
        PureCorrections -> do
          -- OCaml's step verifier: corrections are compile-time constants,
          -- summed via pure curve arithmetic (no seal gates), with the
          -- final CompleteAdd deferred to the end.
          --
          -- Per-branch (in-circuit) corrections are not expected here —
          -- the step circuit isn't multi-branch.
          let
            rawCorrectionPts = Array.mapMaybe
              ( case _ of
                  AddWithCorrection r -> Just r.correction
                  AddWithCircuitCorrection _ ->
                    unsafeThrow "PublicInputCommit: AddWithCircuitCorrection not supported in PureCorrections mode"
                  CondAdd _ _ -> Nothing
              )
              (NEA.toArray results')
          correctionPtsN <- case NEA.fromArray rawCorrectionPts of
            Just nea -> pure nea
            Nothing -> unsafeThrow "PublicInputCommit: rawCorrectionPts non-empty (≥1 AddWithCorrection expected in results')"
          let corrHead = NEA.head correctionPtsN
          let corrTail = NEA.tail correctionPtsN

          -- Phase 1: Execute all scaleFast2' calls, collecting results.
          --   This generates VarBaseMul + internal CompleteAdd gates.
          evaluated <- for results' \term -> case term of
            AddWithCorrection { scaleMul: DeferredScaleMul doScaleMul } ->
              Left <$> doScaleMul
            AddWithCircuitCorrection _ ->
              unsafeThrow "PublicInputCommit: AddWithCircuitCorrection not supported in PureCorrections mode"
            CondAdd b lagrangePt ->
              pure (Right { b, lagrangePt })

          -- Phase 2: Reduce results pairwise with addComplete.
          --   Matches OCaml's List.reduce_exn ~f:(fun (_,b1) (_,b2) -> (_, add_fast b1 b2)).
          --   Corrections are summed as pure constants in parallel.
          let { head: first, tail: rest } = NEA.uncons evaluated
          acc <- foldM
            ( \acc result -> case result of
                Left point -> _.p <$> addComplete acc point
                Right { b, lagrangePt } -> do
                  added <- _.p <$> addComplete lagrangePt acc
                  y' <- if_ b added.y acc.y
                  x' <- if_ b added.x acc.x
                  pure { x: x', y: y' }
            )
            (fromLeft (constPt corrHead) first)
            rest

          -- Phase 3: Add total correction (constant) to accumulator.
          let correctionPt = constPt $ foldl (addPurePt params.curveParams) corrHead corrTail
          accWithCorr <- _.p <$> addComplete acc correctionPt

          -- Negate and add blinding generator
          negAcc <- Curves.negate accWithCorr
          _.p <$> addComplete negAcc (constPt params.blindingH)

        InCircuitCorrections -> do
          -- Wrap verifier: corrections summed in-circuit, fold interleaved.
          -- Constant corrections (`AddWithCorrection`) get lifted via `constPt`
          -- to FVar form; per-branch corrections (`AddWithCircuitCorrection`)
          -- are already FVar (1-hot summed across branches).
          let
            rawCorrectionPts = Array.mapMaybe
              ( case _ of
                  AddWithCorrection r -> Just (constPt r.correction)
                  AddWithCircuitCorrection r -> Just r.correction
                  CondAdd _ _ -> Nothing
              )
              (NEA.toArray results')
          correctionPtsN <- case NEA.fromArray rawCorrectionPts of
            Just nea -> pure nea
            Nothing -> unsafeThrow "PublicInputCommit: rawCorrectionPts non-empty (≥1 AddWithCorrection expected in results')"
          let ch = NEA.head correctionPtsN
          let ct = NEA.tail correctionPtsN
          init <- foldM (\acc c -> _.p <$> addComplete acc c) ch ct

          acc <- foldM
            ( \acc term -> case term of
                AddWithCorrection { scaleMul: DeferredScaleMul doScaleMul } -> do
                  point <- doScaleMul
                  _.p <$> addComplete acc point
                AddWithCircuitCorrection { scaleMul: DeferredScaleMul doScaleMul } -> do
                  point <- doScaleMul
                  _.p <$> addComplete acc point
                CondAdd b lagrangePt -> do
                  added <- _.p <$> addComplete lagrangePt acc
                  y' <- if_ b added.y acc.y
                  x' <- if_ b added.x acc.x
                  pure { x: x', y: y' }
            )
            init
            results'

          negAcc <- Curves.negate acc
          _.p <$> addComplete negAcc (constPt params.blindingH)

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

-- | Single scalar mul with shift correction.
-- | Fetches one Lagrange base via `lookup idx` and increments the walk
-- | counter by one.
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
  -> LagrangeBaseLookup f
  -> Int
  -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)
scalarMulLeaf params scalar lookup idx = do
  let
    base = lookup idx
    actualShift = reflectType (Proxy @bitsUsed)
    scaleMul = DeferredScaleMul (scaleFast2' @nChunks @sDiv2Bits base.circuit scalar)
    term = case base.correctionAt of
      Nothing ->
        let
          correction = wrapPt $ EC.negate_ $ unwrapPt
            $ pow2pow params base.constant actualShift
        in
          AddWithCorrection { scaleMul, correction }
      Just corrFn ->
        AddWithCircuitCorrection { scaleMul, correction: corrFn actualShift }
  pure
    { results: [ term ]
    , nextIdx: idx + 1
    }

constPt :: forall f. PrimeField f => AffinePoint (F f) -> AffinePoint (FVar f)
constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }

unwrapPt :: forall f. AffinePoint (F f) -> AffinePoint f
unwrapPt { x: F x', y: F y' } = { x: x', y: y' }

wrapPt :: forall f. AffinePoint f -> AffinePoint (F f)
wrapPt { x, y } = { x: F x, y: F y }

-- | Pure affine addition for summing constant correction points.
-- | Handles the doubling case (same point) via EC.double.
addPurePt :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> AffinePoint (F f) -> AffinePoint (F f)
addPurePt params p1 p2
  | unwrapPt p1 == unwrapPt p2 = EC.double params p1
  | otherwise = wrapPt $ unsafePartial $ fromJust $ EC.toAffine $ unsafePartial (EC.addAffine (unwrapPt p1) (unwrapPt p2))

-- | Compute [2^k] * p by iterating pure doubling.
pow2pow :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> Int -> AffinePoint (F f)
pow2pow _ p k
  | k <= 0 = p
pow2pow params p k = pow2pow params (EC.double params p) (k - 1)
