-- | The step circuit's per-proof witness — one previous proof's wrap
-- | proof, deferred values, evaluations and carried-over challenges —
-- | and the types it is assembled from.
-- |
-- | Each newtype here exists to pin a wire order: a bare record takes
-- | `RCircuitType`'s alphabetical field order, so swapping a newtype
-- | for its record compiles and silently changes the encoding.
module Pickles.Step.Types
  ( UnfinalizedFieldCount
  , AllocBranchData(..)
  , WrapProof(..)
  , FopProofState(..)
  , ProofState(..)
  , PerProofWitness(..)
  , perProofWitnessTyp
  , chunkedEvalsTyp
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Fin (getFinite, unsafeFinite)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple5, tuple10, tuple2, tuple3, tuple5, uncurry10, uncurry2, uncurry3, uncurry5)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.DeferredValues (BranchData)
import Pickles.Field (StepField)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Typ (Typ, arrayTyp, pairTyp, transportTyp, typOf, unitTyp)
import Pickles.Types (ChunkedEvals, WrapProofMessages, WrapProofOpening)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, UnChecked, const_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Type.Proxy (Proxy(..))

-- | Step-field scalars one `PerProofUnfinalized` occupies in the step
-- | circuit's public input.
type UnfinalizedFieldCount = 32

-- | `BranchData` at the order the step circuit allocates it in: the two
-- | mask bits, then `domainLog2`. The newtype exists only to pin that
-- | order — the record's own alphabetical order puts `domainLog2`
-- | first, and the swap compiles.
newtype AllocBranchData f b = AllocBranchData (BranchData f b)

-- | The record holds the mask as a `Vector 2`, so this pair is where
-- | the record's order and the wire order meet.
branchTuple :: forall f b. BranchData f b -> Tuple3 b b f
branchTuple r = tuple3
  (r.proofsVerifiedMask !! unsafeFinite @2 0)
  (r.proofsVerifiedMask !! unsafeFinite @2 1)
  r.domainLog2

tupleBranch :: forall f b. Tuple3 b b f -> AllocBranchData f b
tupleBranch = uncurry3 \mask0 mask1 domainLog2 ->
  AllocBranchData { domainLog2, proofsVerifiedMask: mask0 :< mask1 :< Vector.nil }

instance
  ( CircuitType f a fvar
  , CircuitType f b bvar
  ) =>
  CircuitType f (AllocBranchData a b) (AllocBranchData fvar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple3 b b a))
  valueToFields (AllocBranchData r) = genericValueToFields (branchTuple r)
  fieldsToValue fs = tupleBranch (genericFieldsToValue fs :: Tuple3 b b a)
  varToFields (AllocBranchData r) = genericVarToFields @(Tuple3 b b a) (branchTuple r)
  fieldsToVar fs = tupleBranch (genericFieldsToVar @(Tuple3 b b a) fs :: Tuple3 bvar bvar fvar)

instance
  ( FieldSizeInBits f n
  , Compare 16 n LT
  , HasEndo basef f
  , CheckedType f (KimchiConstraint f) (Tuple3 (BoolVar f) (BoolVar f) (FVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (AllocBranchData (FVar f) (BoolVar f)) where
  check (AllocBranchData r) = label "branch-data-check" do
    -- Booleanity on the two masks; a no-op on `domainLog2`.
    check (branchTuple r)
    -- `domainLog2` is range-checked instead by expanding its 16 bits
    -- through the endo.
    let EndoScalar e = endoScalar @basef @f
    _ <- EndoScalar.toField @1 (unsafePartial (unsafeFromField r.domainLog2) :: SizedF 16 (FVar f)) (const_ e)
    pure unit

-- | A wrap proof: the prover's commitments and the opening proof, in
-- | that order. `n` is the opening's IPA round count.
newtype WrapProof :: Int -> Int -> Type -> Type -> Type
newtype WrapProof n stepChunks pt sf = WrapProof
  -- | `stepChunks` is the chunk count of these commitments. Every call
  -- | site instantiates it at `Pickles.Types.WrapVkChunks`.
  { messages :: WrapProofMessages stepChunks pt
  , opening :: WrapProofOpening n pt sf
  }

instance
  ( CircuitType f a avar
  , CircuitType f b bvar
  , Reflectable n Int
  , Reflectable stepChunks Int
  ) =>
  CircuitType f (WrapProof n stepChunks a b) (WrapProof n stepChunks avar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple2 (WrapProofMessages stepChunks a) (WrapProofOpening n a b)))
  valueToFields (WrapProof r) = genericValueToFields (tuple2 r.messages r.opening)
  fieldsToValue fs =
    let
      tup :: Tuple2 (WrapProofMessages stepChunks a) (WrapProofOpening n a b)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup
  varToFields (WrapProof r) = genericVarToFields @(Tuple2 (WrapProofMessages stepChunks a) (WrapProofOpening n a b)) (tuple2 r.messages r.opening)
  fieldsToVar fs =
    let
      tup :: Tuple2 (WrapProofMessages stepChunks avar) (WrapProofOpening n avar bvar)
      tup = genericFieldsToVar @(Tuple2 (WrapProofMessages stepChunks a) (WrapProofOpening n a b)) fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup

instance
  ( CheckedType f c avar
  , CheckedType f c bvar
  , Reflectable n Int
  ) =>
  CheckedType f c (WrapProof n stepChunks avar bvar) where
  check (WrapProof r) = check (tuple2 r.messages r.opening)

-- | One previous proof's deferred values and sponge digest, at the
-- | order the step circuit allocates them in.
-- |
-- | The `UnChecked (SizedF 128 f)` fields are claimed to be 128 bits
-- | but are not range-checked at allocation.
newtype FopProofState (d :: Int) f = FopProofState
  { combinedInnerProduct :: f
  , b :: f
  , zetaToSrsLength :: f
  , zetaToDomainSize :: f
  , perm :: f
  , spongeDigest :: f
  , beta :: UnChecked (SizedF 128 f)
  , gamma :: UnChecked (SizedF 128 f)
  , alpha :: UnChecked (SizedF 128 f)
  , zeta :: UnChecked (SizedF 128 f)
  , xi :: UnChecked (SizedF 128 f)
  , bulletproofChallenges :: Vector d (UnChecked (SizedF 128 f))
  }

-- | `FopProofState`'s wire shape, at value (`x = F f`) or variable
-- | (`x = FVar f`) elements.
type FopProofStateTuple d x =
  Tuple2
    (Tuple10 x x x x x x (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)))
    (Tuple2 (UnChecked (SizedF 128 x)) (Vector d (UnChecked (SizedF 128 x))))

instance
  ( FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f (FopProofState d (F f)) (FopProofState d (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FopProofStateTuple d (F f)))
  valueToFields (FopProofState r) = genericValueToFields
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )
  fieldsToValue fs =
    let
      tup :: FopProofStateTuple d (F f)
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \t10 t2 ->
            uncurry10
              ( \cip b zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry2
                    ( \xi bulletproofChallenges ->
                        FopProofState { combinedInnerProduct: cip, b, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges }
                    )
                    t2
              )
              t10
        )
        tup
  varToFields (FopProofState r) = genericVarToFields
    @(FopProofStateTuple d (F f))
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )
  fieldsToVar fs =
    let
      tup :: FopProofStateTuple d (FVar f)
      tup = genericFieldsToVar @(FopProofStateTuple d (F f)) fs
    in
      uncurry2
        ( \t10 t2 ->
            uncurry10
              ( \cip b zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry2
                    ( \xi bulletproofChallenges ->
                        FopProofState { combinedInnerProduct: cip, b, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges }
                    )
                    t2
              )
              t10
        )
        tup

instance (CheckedType f c var) => CheckedType f c (FopProofState d var) where
  check (FopProofState r) = check
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )

-- | One previous proof's deferred values together with its branch
-- | data, in that order.
-- |
-- | `d` is the step IPA round count — structurally always
-- | `StepIPARounds` for the Pasta cycle, but left polymorphic so
-- | `Pickles.Prove.Step` and friends can stay polymorphic too and
-- | concretize only at their top-level bindings.
newtype ProofState (d :: Int) f b = ProofState
  { fopState :: FopProofState d f
  , branchData :: AllocBranchData f b
  }

instance
  ( FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f (ProofState d (F f) Boolean) (ProofState d (FVar f) (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (FopProofState d (F f)) (AllocBranchData (F f) Boolean)))
  valueToFields (ProofState r) = genericValueToFields (tuple2 r.fopState r.branchData)
  fieldsToValue fs =
    let
      tup :: Tuple2 (FopProofState d (F f)) (AllocBranchData (F f) Boolean)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\fopState branchData -> ProofState { fopState, branchData }) tup
  varToFields (ProofState r) = genericVarToFields
    @(Tuple2 (FopProofState d (F f)) (AllocBranchData (F f) Boolean))
    (tuple2 r.fopState r.branchData)
  fieldsToVar fs =
    let
      tup :: Tuple2 (FopProofState d (FVar f)) (AllocBranchData (FVar f) (BoolVar f))
      tup = genericFieldsToVar @(Tuple2 (FopProofState d (F f)) (AllocBranchData (F f) Boolean)) fs
    in
      uncurry2 (\fopState branchData -> ProofState { fopState, branchData }) tup

instance
  ( CheckedType f (KimchiConstraint f) (FopProofState d (FVar f))
  , CheckedType f (KimchiConstraint f) (AllocBranchData (FVar f) (BoolVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (ProofState d (FVar f) (BoolVar f)) where
  check (ProofState r) = check (tuple2 r.fopState r.branchData)

-- | Everything the step circuit allocates for one previous proof: that
-- | proof's wrap proof, its deferred values and branch data, its
-- | evaluations, and the challenges and commitments carried over from
-- | the proofs it itself verified.
-- |
-- | `ds` is the step-side IPA round count (`StepIPARounds`) and `dw` the
-- | wrap-side one (`WrapIPARounds`). Both stay polymorphic so only
-- | top-level bindings name the Pasta constants.
newtype PerProofWitness (stepChunks :: Int) (ds :: Int) (dw :: Int) f sf b = PerProofWitness
  { wrapProof :: WrapProof dw stepChunks (WeierstrassAffinePoint PallasG f) sf
  , proofState :: ProofState ds f b
  -- | Every chunk of the previous step proof's evaluations. The chunk
  -- | count is not in the type: like the width, it reaches the circuit
  -- | through `perProofWitnessTyp`.
  , prevEvals :: ChunkedEvals f
  -- | One entry per previous proof this slot's own wrap proof
  -- | verified. The width is not in the type: it comes from the
  -- | application spec and reaches the circuit through
  -- | `perProofWitnessTyp`.
  , prevChallenges :: Array (UnChecked (Vector ds f))
  , prevSgs :: Array (WeierstrassAffinePoint PallasG f)
  }

-- | `PerProofWitness`'s field order, as a nested tuple, and the order
-- | `perProofWitnessTyp` lays the fields out in. Not a `CircuitType`:
-- | `prevEvals`, `prevChallenges` and `prevSgs` hold arrays, so nothing
-- | can size them from the type alone.
type PerProofWitnessTuple stepChunks ds dw x sf b =
  Tuple5
    (WrapProof dw stepChunks (WeierstrassAffinePoint PallasG x) sf)
    (ProofState ds x b)
    (ChunkedEvals x)
    (Array (UnChecked (Vector ds x)))
    (Array (WeierstrassAffinePoint PallasG x))

perProofWitnessTuple
  :: forall stepChunks ds dw x sf b
   . PerProofWitness stepChunks ds dw x sf b
  -> PerProofWitnessTuple stepChunks ds dw x sf b
perProofWitnessTuple (PerProofWitness r) =
  tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs

perProofWitnessOfTuple
  :: forall stepChunks ds dw x sf b
   . PerProofWitnessTuple stepChunks ds dw x sf b
  -> PerProofWitness stepChunks ds dw x sf b
perProofWitnessOfTuple = uncurry5
  \wrapProof proofState prevEvals prevChallenges prevSgs ->
    PerProofWitness { wrapProof, proofState, prevEvals, prevChallenges, prevSgs }

-- | `ChunkedEvals` as a `Typ`, at `numChunks` chunks per evaluation.
-- |
-- | The columns run in `AllocEvals`'s order: public, witness,
-- | coefficients, `z`, sigma, index, then `ftEval1`. Within a column
-- | the `zeta` chunks come before the `omega*zeta` chunks, so at one
-- | chunk the layout is `AllocEvals`'s.
chunkedEvalsTyp
  :: forall f c
   . Int
  -> Typ f c (ChunkedEvals (F f)) (ChunkedEvals (FVar f))
chunkedEvalsTyp numChunks =
  { size: columnCount * columnSize + 1
  , toFields: \e ->
      map (\(F x) -> x)
        (Array.concatMap columnFields (columns e) <> [ e.ftEval1 ])
  , fromVars: \vars ->
      let
        column i = columnOfFields
          (Array.slice (i * columnSize) ((i + 1) * columnSize) vars)

        columnVec :: forall n. Reflectable n Int => Int -> Vector n (NonEmptyArray (PointEval (FVar f)))
        columnVec from = Vector.generate \j -> column (from + getFinite j)
      in
        { publicEvals: column 0
        , witnessEvals: columnVec 1
        , coeffEvals: columnVec 16
        , zEvals: column 31
        , sigmaEvals: columnVec 32
        , indexEvals: columnVec 38
        , ftEval1: fromJust' "chunkedEvalsTyp: ftEval1"
            (Array.index vars (columnCount * columnSize))
        }
  , check: \_ -> pure unit
  }
  where
  columnCount = 44
  columnSize = 2 * numChunks

  columns :: forall a. ChunkedEvals a -> Array (NonEmptyArray (PointEval a))
  columns e =
    [ e.publicEvals ]
      <> Vector.toUnfoldable e.witnessEvals
      <> Vector.toUnfoldable e.coeffEvals
      <> [ e.zEvals ]
      <> Vector.toUnfoldable e.sigmaEvals
      <> Vector.toUnfoldable e.indexEvals

  columnFields :: forall a. NonEmptyArray (PointEval a) -> Array a
  columnFields chunks =
    let
      arr = NEA.toArray chunks
    in
      map _.zeta arr <> map _.omegaTimesZeta arr

  columnOfFields :: forall a. Array a -> NonEmptyArray (PointEval a)
  columnOfFields fs =
    fromJust' "chunkedEvalsTyp: a column needs at least one chunk"
      $ NEA.fromArray
      $ Array.zipWith (\zeta omegaTimesZeta -> { zeta, omegaTimesZeta })
          (Array.take numChunks fs)
          (Array.drop numChunks fs)

-- | A slot's per-proof witness as a `Typ`. The wrap proof and the
-- | proof state come from `CircuitType`; the two arrays are sized by
-- | `width` and the evaluations by `numChunks`.
perProofWitnessTyp
  :: forall stepChunks ds dw sf sfvar
   . Reflectable ds Int
  => CircuitType StepField
       (WrapProof dw stepChunks (WeierstrassAffinePoint PallasG (F StepField)) sf)
       (WrapProof dw stepChunks (WeierstrassAffinePoint PallasG (FVar StepField)) sfvar)
  => CheckedType StepField (KimchiConstraint StepField)
       (WrapProof dw stepChunks (WeierstrassAffinePoint PallasG (FVar StepField)) sfvar)
  => CircuitType StepField
       (ProofState ds (F StepField) Boolean)
       (ProofState ds (FVar StepField) (BoolVar StepField))
  => CheckedType StepField (KimchiConstraint StepField)
       (ProofState ds (FVar StepField) (BoolVar StepField))
  => { width :: Int, numChunks :: Int }
  -> Typ StepField (KimchiConstraint StepField)
       (PerProofWitness stepChunks ds dw (F StepField) sf Boolean)
       (PerProofWitness stepChunks ds dw (FVar StepField) sfvar (BoolVar StepField))
perProofWitnessTyp { width, numChunks } =
  transportTyp
    perProofWitnessTuple
    perProofWitnessOfTuple
    perProofWitnessTuple
    ( pairTyp typOf
        ( pairTyp typOf
            ( pairTyp (chunkedEvalsTyp numChunks)
                ( pairTyp (arrayTyp width typOf)
                    (pairTyp (arrayTyp width typOf) unitTyp)
                )
            )
        )
    )
