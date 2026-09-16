-- | The public input commitment: a lagrange-basis MSM, with the scalar
-- | width chosen per leaf of the statement type.
-- |
-- | Bases are consumed by index, left to right in `RowList`
-- | (alphabetical) field order — the same order `CircuitType`
-- | serialises the statement in, which is what pairs basis index `i`
-- | with public input slot `i`. The walk threads an `Int` counter
-- | through the instances and calls a `LagrangeBaseLookup` closure
-- | whenever it needs a base, so there is no pre-sized array.
module Pickles.PublicInputCommit
  ( class PublicInputCommit
  , class RPublicInputCommit
  , class PackStatement
  , class RPackStatement
  , PackedField
  , CorrectionMode(..)
  , DeferredScaleMul1(..)
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
  , mkSideloadedLagrangeLookup
  , sumMaskedAffine
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
import Data.Traversable (for, sequence)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Mul)
import Prim.Row as Row
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, Snarky, addConstraint, const_, if_, label)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.Kimchi.AddComplete (addComplete, sealPoint)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Constraint.Basic (boolean) as Basic
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..), CurveParams)
import Snarky.Data.EllipticCurve as EC
import Snarky.Data.EllipticCurve.Projective (doubleProjective)
import Snarky.Types.Shifted (SplitField(..), Type1(..), Type2(..))
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- Packing
-------------------------------------------------------------------------------

-- | A leaf of a structured public input, tagged with the scalar width
-- | its MSM term needs.
data PackedField f
  = FullField (FVar f) -- ^ full 255-bit field element
  | PackedBits (FVar f) Int -- ^ value of the given bit width
  | SplitShifted (FVar f) (BoolVar f) -- ^ shifted scalar: `sDiv2` + `sOdd`

-- | The leaves of a structured public input, flattened in field order.
-- | Packing only: no constraints, no MSM.
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
-- MSM terms
-------------------------------------------------------------------------------

-- | How `publicInputCommit` sums the shift corrections.
-- | `PureCorrections` sums them as constants, off-circuit (step);
-- | `InCircuitCorrections` sums them with `addComplete` gates (wrap).
data CorrectionMode = PureCorrections | InCircuitCorrections

-- | One chunk's scalar multiplication, held unrun so that the
-- | commitment fold can interleave it with the accumulator's
-- | `addComplete` chunk by chunk.
newtype DeferredScaleMul1 f = DeferredScaleMul1
  ( forall r
     . PrimeField f
    => Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
  )

-- | One term of the public input MSM, per leaf of the statement.
-- |
-- |   * `AddWithCorrection` — the shift correction is a compile-time
-- |     constant. Produced when `LagrangeBase.correctionAt` is
-- |     `Nothing`: one branch, or all branch domains equal.
-- |
-- |   * `AddWithCircuitCorrection` — the correction is an in-circuit
-- |     point, already 1-hot summed across branches. Produced when
-- |     `correctionAt` is `Just`, for a wrap circuit whose branch
-- |     domains differ.
-- |
-- |   * `CondAdd` — a one-bit leaf. Its lagrange point is always
-- |     masked; there is no all-domains-equal fast path for it.
-- |
-- | Every variant carries `Vector stepChunks` of points, so the fold
-- | can run one accumulator per chunk.
data MsmTerm (stepChunks :: Int) f
  = AddWithCorrection { scaleMuls :: Vector stepChunks (DeferredScaleMul1 f), correction :: Vector stepChunks (AffinePoint (F f)) }
  | AddWithCircuitCorrection { scaleMuls :: Vector stepChunks (DeferredScaleMul1 f), correction :: Vector stepChunks (AffinePoint (FVar f)) }
  | CondAdd (BoolVar f) (Vector stepChunks (AffinePoint (FVar f)))

-- | The lagrange base at one public input index, in the forms the MSM
-- | needs it. Each field is chunked: `Vector stepChunks` of points,
-- | one per slice of the commitment.
-- |
-- |   * `constant` — the compile-time point, source of the constant
-- |     correction.
-- |   * `circuit` — the point `scaleFast2'` scales. `constPt constant`
-- |     on the single-branch path; the 1-hot sum
-- |     `Σ_b whichBranch[b] * lagrange(domain[b], i)` per branch.
-- |   * `condAddPt` — the point a `CondAdd` leaf uses. Always that
-- |     1-hot sum, even when every domain is equal, because
-- |     `whichBranch` is a non-trivial one-hot vector there too.
-- |   * `correctionAt` — `Nothing` on the single-branch path, where the
-- |     caller derives the correction from `constant` via `pow2pow`.
-- |     `Just f` on the per-branch path: `f shift` is the in-circuit
-- |     `-Σ_b whichBranch[b] * [2^shift] * lagrange(domain[b], i)`.
-- |   * `sealCondAddPt` — whether a `CondAdd` leaf seals `condAddPt`
-- |     before use. Set for a step side-loaded slot; clear for wrap
-- |     multi-branch, where only `scalarMulLeaf`'s bases are sealed.
type LagrangeBase :: Int -> Type -> Type
type LagrangeBase stepChunks f =
  { constant :: Vector stepChunks (AffinePoint (F f))
  , circuit :: Vector stepChunks (AffinePoint (FVar f))
  , condAddPt :: Vector stepChunks (AffinePoint (FVar f))
  , correctionAt :: Maybe (Int -> Vector stepChunks (AffinePoint (FVar f)))
  , sealCondAddPt :: Boolean
  }

-- | The lagrange base at a given public input index.
type LagrangeBaseLookup :: Int -> Type -> Type
type LagrangeBaseLookup stepChunks f = Int -> LagrangeBase stepChunks f

-- | A base with no per-branch dispatch: one compile-time point, lifted
-- | into `circuit` and `condAddPt` by `constPt`.
mkConstLagrangeBase
  :: forall stepChunks f
   . PrimeField f
  => Vector stepChunks (AffinePoint (F f))
  -> LagrangeBase stepChunks f
mkConstLagrangeBase pts =
  { constant: pts
  , circuit: map constPt pts
  , condAddPt: map constPt pts
  , correctionAt: Nothing
  , sealCondAddPt: false
  }

-- | A lookup built from a function giving the chunked `i`-th lagrange
-- | commitment — typically `srsLagrangeCommitmentChunksAt srs
-- | domainLog2`, whose `Array` of chunks the caller reshapes into
-- | `Vector stepChunks`.
mkConstLagrangeBaseLookup
  :: forall stepChunks f
   . PrimeField f
  => (Int -> Vector stepChunks (AffinePoint (F f)))
  -> LagrangeBaseLookup stepChunks f
mkConstLagrangeBaseLookup f i = mkConstLagrangeBase (f i)

-- | `Σᵢ bᵢ * pᵢ` over a one-hot bitvec and constant points, coordinate
-- | by coordinate. Pure `CVar.scale_` and `CVar.add_`, so it emits no
-- | constraints.
sumMaskedAffine
  :: forall n m f
   . PrimeField f
  => Add 1 m n
  => Vector n (BoolVar f)
  -> Vector n (AffinePoint (F f))
  -> AffinePoint (FVar f)
sumMaskedAffine bits perBranchPts =
  let
    boolFvars = map (coerce) bits

    scaledPts = Vector.zipWith
      ( \b (AffinePoint { x: F x', y: F y' }) ->
          { x: CVar.scale_ x' b, y: CVar.scale_ y' b }
      )
      boolFvars
      perBranchPts
    { head: spHead, tail: spTail } = Vector.uncons scaledPts
  in
    AffinePoint
      ( foldl
          ( \acc pt ->
              { x: CVar.add_ acc.x pt.x, y: CVar.add_ acc.y pt.y }
          )
          spHead
          spTail
      )

-- | A lookup for a side-loaded slot: a one-hot mux across the three
-- | per-domain lagrange tables `actualWrapDomainSize ∈ {N0, N1, N2}`,
-- | with the correction at `2^shift` sum-masked the same way.
-- |
-- | Its bases set `correctionAt`, which routes `scalarMulLeaf` through
-- | `AddWithCircuitCorrection`, so callers must pass
-- | `InCircuitCorrections`.
mkSideloadedLagrangeLookup
  :: forall @slotVkChunks f
   . PrimeField f
  => Reflectable slotVkChunks Int
  => CurveParams f
  -> Vector 3 (BoolVar f)
  -> Vector 3 (Int -> Vector slotVkChunks (AffinePoint (F f)))
  -> LagrangeBaseLookup slotVkChunks f
mkSideloadedLagrangeLookup curveP bits perDomainAt i =
  let
    perDomainChunks = map (\at -> at i) perDomainAt

    -- For each chunk index, 1-hot mux across the 3 domains.
    chunkedSumMask
      :: Vector 3 (Vector slotVkChunks (AffinePoint (F f)))
      -> Vector slotVkChunks (AffinePoint (FVar f))
    chunkedSumMask v3 =
      Vector.generate \ci ->
        sumMaskedAffine bits (map (\vc -> vc !! ci) v3)

    summed = chunkedSumMask perDomainChunks
    correctionAt shift =
      chunkedSumMask
        ( map
            ( map
                ( \pt ->
                    wrapPt $ EC.negate_ $ unwrapPt
                      $ pow2pow curveP pt shift
                )
            )
            perDomainChunks
        )
  in
    { -- `constant` is never read on the per-branch path — only
      -- `circuit`, `condAddPt` and `correctionAt` drive the commitment
      -- there — so the head domain's points stand in for it.
      constant: (Vector.uncons perDomainChunks).head
    , circuit: summed
    , condAddPt: summed
    , correctionAt: Just correctionAt
    , sealCondAddPt: true
    }

-- | The MSM terms from a walk, and the first lagrange base index the
-- | walk did not consume.
type ScalarMulResult :: Int -> Type -> Type
type ScalarMulResult stepChunks f =
  { results :: Array (MsmTerm stepChunks f)
  , nextIdx :: Int
  }

-------------------------------------------------------------------------------
-- The walk
-------------------------------------------------------------------------------

-- | The MSM terms of a structured public input, each leaf scaled at
-- | the width its type allows. `idx` is the walk position: a leaf takes
-- | its base from `lookup idx` and returns the next free index.
class PublicInputCommit a f where
  scalarMuls
    :: forall @stepChunks r
     . PrimeField f
    => Reflectable stepChunks Int
    => CurveParams f
    -> a
    -> LagrangeBaseLookup stepChunks f
    -> Int
    -> Snarky f (KimchiConstraint f) r (ScalarMulResult stepChunks f)

-------------------------------------------------------------------------------
-- Leaf instances
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

-- | Conditionally adds the lagrange point. The booleanity constraint
-- | is emitted during the walk, so that it precedes the correction sum
-- | and the fold in the gate stream.
instance PublicInputCommit (BoolVar f) f where
  scalarMuls _ bool lookup idx = do
    addConstraint (Basic.boolean (coerce bool :: FVar f))
    let base = lookup idx
    pt <-
      if base.sealCondAddPt then for base.condAddPt sealPoint
      else pure base.condAddPt
    pure { results: [ CondAdd bool pt ], nextIdx: idx + 1 }

-- | Shifted scalar (Type1): one field element, 255 bits → 51 chunks,
-- | sDiv2Bits = 254.
instance (FieldSizeInBits f 255) => PublicInputCommit (Type1 (FVar f)) f where
  scalarMuls params (Type1 fv) lookup idx = scalarMulLeaf @51 @254 params fv lookup idx

-- | Shifted scalar (SplitField): `sDiv2` at full width, 255 bits → 51
-- | chunks, then `sOdd` as a conditional add. `sDiv2 = (s - sOdd) / 2`
-- | reaches 254 bits for `combinedInnerProduct`, `b`, `perm`,
-- | `zetaToSrsLength` and `zetaToDomainSize`.
-- |
-- | The two bases are consumed in alphabetical order, `sDiv2` before
-- | `sOdd`, which is the order `CircuitType` serialises the record in.
instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (SplitField (FVar f) (BoolVar f)) f where
  scalarMuls params (SplitField { sDiv2, sOdd }) lookup idx = do
    { results: r1, nextIdx: idx1 } <- scalarMulLeaf @51 @254 params sDiv2 lookup idx
    addConstraint (Basic.boolean (coerce sOdd :: FVar f))
    let oddBase = lookup idx1
    pt <-
      if oddBase.sealCondAddPt then for oddBase.condAddPt sealPoint
      else pure oddBase.condAddPt
    pure
      { results: r1 <> [ CondAdd sOdd pt ]
      , nextIdx: idx1 + 1
      }

instance (FieldSizeInBits f 255, PrimeField f) => PublicInputCommit (Type2 (SplitField (FVar f) (BoolVar f))) f where
  scalarMuls params (Type2 sf) lookup idx = scalarMuls params sf lookup idx

-------------------------------------------------------------------------------
-- Structural instances
-------------------------------------------------------------------------------

instance (PublicInputCommit a f, PublicInputCommit b f) => PublicInputCommit (Tuple a b) f where
  scalarMuls params (Tuple a b) lookup idx = do
    { results: r1, nextIdx: idx1 } <- scalarMuls params a lookup idx
    { results: r2, nextIdx: idx2 } <- scalarMuls params b lookup idx1
    pure { results: r1 <> r2, nextIdx: idx2 }

instance PublicInputCommit Unit f where
  scalarMuls _ _ _ idx = pure { results: [], nextIdx: idx }

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

-- | Record: fields in `RowList` (alphabetical) order.
instance
  ( RL.RowToList r rl
  , RPublicInputCommit rl f r
  ) =>
  PublicInputCommit (Record r) f where
  scalarMuls params rec lookup idx = rScalarMuls @rl params rec lookup idx

-------------------------------------------------------------------------------
-- RowList walker
-------------------------------------------------------------------------------

class RPublicInputCommit (rl :: RL.RowList Type) f (r :: Row Type) | rl -> r where
  rScalarMuls
    :: forall @stepChunks rr
     . PrimeField f
    => Reflectable stepChunks Int
    => CurveParams f
    -> Record r
    -> LagrangeBaseLookup stepChunks f
    -> Int
    -> Snarky f (KimchiConstraint f) rr (ScalarMulResult stepChunks f)

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
-- Top-level commitment function
-------------------------------------------------------------------------------

-- | The public input commitment `xHat = -Σᵢ [sᵢ] Bᵢ + blindingH`, with
-- | the shift corrections folded in, one point per chunk.
publicInputCommit
  :: forall @stepChunks a f r cr
   . PublicInputCommit a f
  => PrimeField f
  => Reflectable stepChunks Int
  => { curveParams :: CurveParams f
     , lagrangeAt :: LagrangeBaseLookup stepChunks f
     , blindingH :: AffinePoint (F f)
     , correctionMode :: CorrectionMode
     | r
     }
  -> a
  -> Snarky f (KimchiConstraint f) cr (Vector stepChunks (AffinePoint (FVar f)))
publicInputCommit params input = label "public-input-commit" do
  { results } <- scalarMuls params.curveParams input params.lagrangeAt 0
  case NEA.fromArray results of
    Nothing -> pure (Vector.replicate (constPt params.blindingH))
    Just results' -> unsafePartial do
      case params.correctionMode of
        PureCorrections -> do
          -- Step verifier: corrections are compile-time constants,
          -- summed by pure curve arithmetic and added once at the end,
          -- with one accumulator per chunk. The step circuit is not
          -- multi-branch, so a per-branch correction here is an error.
          let
            rawCorrectionVecs = Array.mapMaybe
              ( case _ of
                  AddWithCorrection r -> Just r.correction
                  AddWithCircuitCorrection _ ->
                    unsafeThrow "PublicInputCommit: AddWithCircuitCorrection not supported in PureCorrections mode"
                  CondAdd _ _ -> Nothing
              )
              (NEA.toArray results')
          correctionPtsN <- case NEA.fromArray rawCorrectionVecs of
            Just nea -> pure nea
            Nothing -> unsafeThrow "PublicInputCommit: rawCorrectionPts non-empty (≥1 AddWithCorrection expected in results')"
          let corrHead = NEA.head correctionPtsN
          let corrTail = NEA.tail correctionPtsN

          -- Phase 1: run every `scaleFast2'`, chunk by chunk.
          evaluated <- for results' \term -> case term of
            AddWithCorrection { scaleMuls } ->
              Left <$> for scaleMuls (\(DeferredScaleMul1 doScaleMul) -> doScaleMul)
            AddWithCircuitCorrection _ ->
              unsafeThrow "PublicInputCommit: AddWithCircuitCorrection not supported in PureCorrections mode"
            CondAdd b lagrangePt ->
              pure (Right { b, lagrangePt })

          -- Phase 2: reduce chunkwise with `addComplete`, muxing the
          -- conditional terms with `if_`.
          let { head: first, tail: rest } = NEA.uncons evaluated
          let initAcc = fromLeft (map constPt corrHead) first
          acc <- foldM
            ( \acc result -> case result of
                Left chunkedPt ->
                  zipWithA
                    (\a p -> _.p <$> addComplete a p)
                    acc
                    chunkedPt
                Right { b, lagrangePt } ->
                  zipWithA
                    ( \a lp -> do
                        AffinePoint added <- _.p <$> addComplete lp a
                        let AffinePoint a' = a
                        y' <- if_ b added.y a'.y
                        x' <- if_ b added.x a'.x
                        pure (AffinePoint { x: x', y: y' })
                    )
                    acc
                    lagrangePt
            )
            initAcc
            rest

          -- Phase 3: add the summed constant correction.
          let
            correctionPtsChunked :: Vector stepChunks (AffinePoint (F f))
            correctionPtsChunked = foldl
              (Vector.zipWith (addPurePt params.curveParams))
              corrHead
              corrTail
          accWithCorr <- zipWithA
            (\a c -> _.p <$> addComplete a (constPt c))
            acc
            correctionPtsChunked

          for accWithCorr \pt -> do
            negPt <- Curves.negate pt
            _.p <$> addComplete negPt (constPt params.blindingH)

        InCircuitCorrections -> do
          -- Wrap verifier: corrections are summed in-circuit. Constant
          -- ones lift through `constPt`; per-branch ones are already
          -- in-circuit points.
          let
            rawCorrectionVecs = Array.mapMaybe
              ( case _ of
                  AddWithCorrection r -> Just (map constPt r.correction)
                  AddWithCircuitCorrection r -> Just r.correction
                  CondAdd _ _ -> Nothing
              )
              (NEA.toArray results')
          correctionPtsN <- case NEA.fromArray rawCorrectionVecs of
            Just nea -> pure nea
            Nothing -> unsafeThrow "PublicInputCommit: rawCorrectionPts non-empty (≥1 AddWithCorrection expected in results')"
          let ch = NEA.head correctionPtsN
          let ct = NEA.tail correctionPtsN
          init <- foldM
            (\acc c -> zipWithA (\a x -> _.p <$> addComplete a x) acc c)
            ch
            ct

          -- Chunk k's `scaleFast2'` and its `addComplete` onto the
          -- accumulator both run before chunk k+1 starts; the gate
          -- stream depends on that interleaving.
          acc <- foldM
            ( \acc term -> case term of
                AddWithCorrection { scaleMuls } ->
                  zipWithA
                    ( \a (DeferredScaleMul1 doScaleMul) -> do
                        pt <- doScaleMul
                        _.p <$> addComplete a pt
                    )
                    acc
                    scaleMuls
                AddWithCircuitCorrection { scaleMuls } ->
                  zipWithA
                    ( \a (DeferredScaleMul1 doScaleMul) -> do
                        pt <- doScaleMul
                        _.p <$> addComplete a pt
                    )
                    acc
                    scaleMuls
                CondAdd b lagrangePt ->
                  zipWithA
                    ( \a lp -> do
                        AffinePoint added <- _.p <$> addComplete lp a
                        let AffinePoint a' = a
                        y' <- if_ b added.y a'.y
                        x' <- if_ b added.x a'.x
                        pure (AffinePoint { x: x', y: y' })
                    )
                    acc
                    lagrangePt
            )
            init
            results'

          for acc \pt -> do
            negPt <- Curves.negate pt
            _.p <$> addComplete negPt (constPt params.blindingH)

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- | One leaf's MSM term, consuming the base at `idx`. `nChunks` sets
-- | the scalar width at `5 * nChunks` bits, and the shift correction is
-- | `-[2^(5 * nChunks)] * base`.
scalarMulLeaf
  :: forall @nChunks @sDiv2Bits f n bitsUsed bitsRemaining sDiv2Remaining stepChunks r
   . FieldSizeInBits f n
  => Add bitsUsed bitsRemaining n
  => Add sDiv2Bits sDiv2Remaining n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => Reflectable stepChunks Int
  => PrimeField f
  => CurveParams f
  -> FVar f
  -> LagrangeBaseLookup stepChunks f
  -> Int
  -> Snarky f (KimchiConstraint f) r (ScalarMulResult stepChunks f)
scalarMulLeaf params scalar lookup idx = do
  let
    base = lookup idx
    actualShift = reflectType (Proxy @bitsUsed)
  term <- case base.correctionAt of
    Nothing ->
      let
        scaleMuls = map
          (\chunkPt -> DeferredScaleMul1 (scaleFast2' @nChunks @sDiv2Bits chunkPt scalar))
          base.circuit
        correction = map
          ( \chunkConst ->
              wrapPt $ EC.negate_ $ unwrapPt
                $ pow2pow params chunkConst actualShift
          )
          base.constant
      in
        pure $ AddWithCorrection { scaleMuls, correction }
    Just corrFn -> do
      -- Correction sealed before base, per chunk: the seal gates land
      -- in that order.
      sealedCorrection <- for (corrFn actualShift) \chunkPt ->
        label "seal-correction" (sealPoint chunkPt)
      sealedBase <- for base.circuit \chunkPt ->
        label "seal-base" (sealPoint chunkPt)
      let
        scaleMuls = map
          (\chunkPt -> DeferredScaleMul1 (scaleFast2' @nChunks @sDiv2Bits chunkPt scalar))
          sealedBase
      pure $ AddWithCircuitCorrection { scaleMuls, correction: sealedCorrection }
  pure
    { results: [ term ]
    , nextIdx: idx + 1
    }

-- | Applicative `zipWith` for `Vector n`.
zipWithA
  :: forall n a b c m
   . Applicative m
  => (a -> b -> m c)
  -> Vector n a
  -> Vector n b
  -> m (Vector n c)
zipWithA f xs ys = sequence (Vector.zipWith f xs ys)

constPt :: forall f. PrimeField f => AffinePoint (F f) -> AffinePoint (FVar f)
constPt (AffinePoint { x: F x', y: F y' }) = AffinePoint { x: const_ x', y: const_ y' }

unwrapPt :: forall f. AffinePoint (F f) -> AffinePoint f
unwrapPt (AffinePoint { x: F x', y: F y' }) = AffinePoint { x: x', y: y' }

wrapPt :: forall f. AffinePoint f -> AffinePoint (F f)
wrapPt (AffinePoint { x, y }) = AffinePoint { x: F x, y: F y }

-- | Affine addition of constant points, falling back to `EC.double`
-- | when the two coincide.
addPurePt :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> AffinePoint (F f) -> AffinePoint (F f)
addPurePt params p1 p2
  | unwrapPt p1 == unwrapPt p2 = EC.double params p1
  | otherwise = wrapPt $ unsafePartial $ fromJust $ EC.toAffine $ unsafePartial (EC.addAffine (unwrapPt p1) (unwrapPt p2))

-- | `[2^k] * p`, by `k` projective doublings and one normalisation —
-- | a single field inversion rather than one per doubling. The affine
-- | result is the same as iterated affine doubling's.
pow2pow :: forall f. PrimeField f => CurveParams f -> AffinePoint (F f) -> Int -> AffinePoint (F f)
pow2pow params p k =
  let
    go pt j
      | j <= 0 = pt
      | otherwise = go (doubleProjective params pt) (j - 1)
  in
    wrapPt $ unsafePartial $ fromJust $ EC.toAffine $ go (EC.fromAffine (unwrapPt p)) k
