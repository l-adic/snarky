-- | Pickles' protocol constants and circuit I/O types for the Pasta
-- | 2-cycle: IPA round counts, chunk counts, commitment curves, the
-- | step and wrap statements, and the allocation carriers those
-- | statements are built from.
module Pickles.Types
  ( StepIPARounds
  , WrapIPARounds
  , WrapVkChunks
  , module ChunkedCommitmentReExports
  , MaxProofsVerified
  , PaddedLength
  , StepCommitmentCurve
  , WrapCommitmentCurve
  , StepInput
  , StepStatement
  , WrapStatement
  , StatementIO(..)
  , WrapProofMessages(..)
  , WrapProofOpening(..)
  , Evals
  , ChunkedEvals
  , AllocEvals(..)
  , PerProofUnfinalized(..)
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple5, Tuple7, tuple10, tuple2, tuple3, tuple5, tuple7, uncurry10, uncurry2, uncurry3, uncurry5, uncurry7)
import Data.Vector (Vector)
import Pickles.DeferredValues (UnfinalizedProof, WrapDeferredValues)
import Pickles.Linearization.FFI (PointEval)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..)) as ChunkedCommitmentReExports
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment)
import Snarky.Circuit.DSL (F, FVar, UnChecked)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

-- | IPA rounds in a step (Tick, Vesta-committed) proof: 16, the log2 of
-- | the Tick SRS size. The step/wrap split is a pickles notion, so the
-- | constant lives here rather than in `snarky-kimchi`.
type StepIPARounds = 16

-- | IPA rounds in a wrap (Tock, Pallas-committed) proof: 15.
type WrapIPARounds = 15

-- | Chunk count of a wrap VK's commitments: 1. A wrap circuit's domain
-- | is 2^13, 2^14 or 2^15 by `max_proofs_verified` and so never exceeds
-- | the Tock SRS, 2^15 (= `WrapIPARounds`), leaving every wrap
-- | polynomial in one chunk.
type WrapVkChunks = 1

-- | The `max_proofs_verified` of a compiled circuit: how many previous
-- | proofs one of its steps verifies. Per circuit, not global.
-- |
-- | Numerically equal to `PaddedLength` at this instantiation but
-- | unrelated to it.
type MaxProofsVerified = 2

-- | The length every slot-indexed vector is padded to before hashing:
-- | 2, Pickles-wide and independent of any circuit's
-- | `max_proofs_verified`. It is the target for each slot's
-- | bp-challenge vector, for the wrap proof's `sgOld` list, and the
-- | ceiling on a proofs-verified prefix mask.
-- |
-- | `Pickles.Wrap.MessageHash.dummyPaddingSpongeStates` accordingly has
-- | `PaddedLength + 1 = 3` entries, for absorbing 0, 1 or 2 dummies.
type PaddedLength = 2

-- | Step proofs commit on Vesta (scalar field `StepField`).
type StepCommitmentCurve = Vesta.G

-- | Wrap proofs commit on Pallas (scalar field `WrapField`).
type WrapCommitmentCurve = Pallas.G

-- | Input to the step circuit combinator: the application input
-- | alongside the witness data for the `n` previous proofs.
-- |
-- | `ds` is phantom here; only `dw` is used, as a previous wrap proof
-- | carries `dw` bulletproof challenges.
type StepInput :: Int -> Type -> Type -> Int -> Int -> Type -> Type -> Type -> Type
type StepInput n input prevInput ds dw f sf b =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  , unfinalizedProofs :: Vector n (UnfinalizedProof dw f sf b)
  , prevChallengeDigests :: Vector n f
  }

-- | The step circuit's output statement, and so part of the public
-- | input the wrap circuit verifies. `Pickles.PackedStatement` carries
-- | the same shape in the field order the wire fixes.
type StepStatement :: Int -> Int -> Int -> Type -> Type -> Type -> Type
type StepStatement n ds dw fv sf b =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv sf b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-- | The wrap circuit's public input statement: wrap deferred values —
-- | including `branchData` — plus the two message digests.
type WrapStatement :: Int -> Type -> Type -> Type -> Type
type WrapStatement d f sf b =
  { proofState ::
      { deferredValues :: WrapDeferredValues d f sf b
      , spongeDigestBeforeEvaluations :: f
      , messagesForNextWrapProof :: f
      }
  , messagesForNextStepProof :: f
  }

-- The allocation carriers below — `StatementIO`, `WrapProofMessages`,
-- `WrapProofOpening`, `AllocEvals`, `PerProofUnfinalized` — are
-- newtypes rather than bare records for one reason: a record picks up
-- `RCircuitType`, which orders fields alphabetically, and that is not
-- the wire order. Each one's `CircuitType`/`CheckedType` instance
-- delegates instead to a nested `Tuple` spelling the wire order out, so
-- replacing a carrier with its record compiles and silently corrupts
-- the encoding.

-- | A rule's statement — the public input to kimchi verify — as its
-- | main function's `input` paired with its returned `output`. The
-- | three public-input modes collapse into this one shape:
-- |
-- |   input only     → StatementIO input Unit
-- |   output only    → StatementIO Unit output
-- |   input + output → StatementIO input output
-- |
-- | `CircuitType Unit Unit` serializes to zero fields, so an unused
-- | side contributes nothing to the public-input array and no mode
-- | needs special-casing.
-- |
-- | `input` precedes `output` on the wire. RowList happens to
-- | alphabetize to the same order, but the instance routes through an
-- | explicit `Tuple2` so the contract does not rest on that
-- | coincidence.
newtype StatementIO input output = StatementIO
  { input :: input
  , output :: output
  }

derive newtype instance (WriteForeign input, WriteForeign output) => WriteForeign (StatementIO input output)
derive newtype instance (ReadForeign input, ReadForeign output) => ReadForeign (StatementIO input output)

instance
  ( CircuitType f inputVal inputVar
  , CircuitType f outputVal outputVar
  ) =>
  CircuitType f
    (StatementIO inputVal outputVal)
    (StatementIO inputVar outputVar) where
  sizeInFields pf _ =
    genericSizeInFields pf (Proxy @(Tuple2 inputVal outputVal))
  valueToFields (StatementIO r) =
    genericValueToFields (tuple2 r.input r.output)
  fieldsToValue fs =
    let
      tup :: Tuple2 inputVal outputVal
      tup = genericFieldsToValue fs
    in
      uncurry2 (\input output -> StatementIO { input, output }) tup
  varToFields (StatementIO r) =
    genericVarToFields @(Tuple2 inputVal outputVal) (tuple2 r.input r.output)
  fieldsToVar fs =
    let
      tup :: Tuple2 inputVar outputVar
      tup = genericFieldsToVar @(Tuple2 inputVal outputVal) fs
    in
      uncurry2 (\input output -> StatementIO { input, output }) tup

instance
  ( CheckedType f c inputVar
  , CheckedType f c outputVar
  ) =>
  CheckedType f c (StatementIO inputVar outputVar) where
  check (StatementIO r) = check (tuple2 r.input r.output)

-- A kimchi polynomial commitment splits into `ceil(domain_size /
-- SRS_max_poly_size)` curve-point chunks. Three distinct such counts
-- run through Pickles and are not interchangeable, so the type variable
-- naming one says which it is:
--
--   * `stepChunks` — compile-wide: the chunks of the step proof a wrap
--     circuit verifies, step domain against wrap SRS.
--
--   * `wrapVkChunks` — compile-wide: this compile's own wrap VK as
--     embedded in the step circuit, pinned to `WrapVkChunks`.
--
--   * `slotVkChunks` — per-slot: one slot's own VK chunk count, carried
--     by `Pickles.Step.VkSource`'s blueprints.
--
-- `ChunkedCommitment` is dimension-agnostic; its parameter is the
-- neutral `chunks`, never one of these three names.

-- | A proof's protocol commitments, as allocated in the per-proof
-- | witness. The wire order is `wComm`, `zComm`, `tComm`.
-- |
-- | `n` is the commitment's `num_chunks` (`docs/chunking.md`): 15
-- | witness polynomials at `n` chunks each, one `z`, and the quotient
-- | polynomial's 7 pieces at `n` chunks each. The nesting is for
-- | reading; `CircuitType` flattens `tComm` to one `7 * n` vector.
newtype WrapProofMessages :: Int -> Type -> Type
newtype WrapProofMessages n pt = WrapProofMessages
  { wComm :: Vector 15 (ChunkedCommitment n pt)
  , zComm :: ChunkedCommitment n pt
  , tComm :: Vector 7 (ChunkedCommitment n pt)
  }

instance
  ( CircuitType f a var
  , Reflectable n Int
  ) =>
  CircuitType f (WrapProofMessages n a) (WrapProofMessages n var) where
  sizeInFields pf _ =
    genericSizeInFields pf (Proxy @(Tuple3 (Vector 15 (ChunkedCommitment n a)) (ChunkedCommitment n a) (Vector 7 (ChunkedCommitment n a))))
  valueToFields (WrapProofMessages r) = genericValueToFields (tuple3 r.wComm r.zComm r.tComm)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 15 (ChunkedCommitment n a)) (ChunkedCommitment n a) (Vector 7 (ChunkedCommitment n a))
      tup = genericFieldsToValue fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup
  varToFields (WrapProofMessages r) =
    genericVarToFields @(Tuple3 (Vector 15 (ChunkedCommitment n a)) (ChunkedCommitment n a) (Vector 7 (ChunkedCommitment n a))) (tuple3 r.wComm r.zComm r.tComm)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 15 (ChunkedCommitment n var)) (ChunkedCommitment n var) (Vector 7 (ChunkedCommitment n var))
      tup = genericFieldsToVar @(Tuple3 (Vector 15 (ChunkedCommitment n a)) (ChunkedCommitment n a) (Vector 7 (ChunkedCommitment n a))) fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup

instance (CheckedType f c var) => CheckedType f c (WrapProofMessages n var) where
  check (WrapProofMessages r) = check (tuple3 r.wComm r.zComm r.tComm)

-- | A proof's bulletproof opening data, as allocated in the per-proof
-- | witness. The wire order is `lr`, `z1`, `z2`, `delta`, `sg`.
-- |
-- | `n` is the IPA round count of the proof being opened:
-- | `StepIPARounds` for a step proof opened inside the wrap circuit,
-- | `WrapIPARounds` for a wrap proof opened inside the step circuit.
newtype WrapProofOpening :: Int -> Type -> Type -> Type
newtype WrapProofOpening n pt sf = WrapProofOpening
  { lr :: Vector n { l :: pt, r :: pt }
  , z1 :: sf
  , z2 :: sf
  , delta :: pt
  , sg :: pt
  }

instance
  ( CircuitType f a avar
  , CircuitType f b bvar
  , Reflectable n Int
  ) =>
  CircuitType f (WrapProofOpening n a b) (WrapProofOpening n avar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple5 (Vector n { l :: a, r :: a }) b b a a))
  valueToFields (WrapProofOpening r) = genericValueToFields (tuple5 r.lr r.z1 r.z2 r.delta r.sg)
  fieldsToValue fs =
    let
      tup :: Tuple5 (Vector n { l :: a, r :: a }) b b a a
      tup = genericFieldsToValue fs
    in
      uncurry5 (\lr z1 z2 delta sg -> WrapProofOpening { lr, z1, z2, delta, sg }) tup
  varToFields (WrapProofOpening r) = genericVarToFields @(Tuple5 (Vector n { l :: a, r :: a }) b b a a) (tuple5 r.lr r.z1 r.z2 r.delta r.sg)
  fieldsToVar fs =
    let
      tup :: Tuple5 (Vector n { l :: avar, r :: avar }) bvar bvar avar avar
      tup = genericFieldsToVar @(Tuple5 (Vector n { l :: a, r :: a }) b b a a) fs
    in
      uncurry5 (\lr z1 z2 delta sg -> WrapProofOpening { lr, z1, z2, delta, sg }) tup

instance
  ( CheckedType f c avar
  , CheckedType f c bvar
  , Reflectable n Int
  ) =>
  CheckedType f c (WrapProofOpening n avar bvar) where
  check (WrapProofOpening r) = check (tuple5 r.lr r.z1 r.z2 r.delta r.sg)

-- | The evaluation block of a kimchi proof, one `PointEval` per
-- | polynomial: public input, the 15 witness columns, the 15
-- | coefficients, `z`, the 6 sigmas, the 6 index selectors, and
-- | `ftEval1`.
-- |
-- | Field order here is cosmetic. The wire order is pinned by the
-- | `Tuple7` in `AllocEvals`'s `CircuitType` instance, never by
-- | RowList.
type Evals a =
  { publicEvals :: PointEval a
  , witnessEvals :: Vector 15 (PointEval a)
  , coeffEvals :: Vector 15 (PointEval a)
  , zEvals :: PointEval a
  , sigmaEvals :: Vector 6 (PointEval a)
  , indexEvals :: Vector 6 (PointEval a)
  , ftEval1 :: a
  }

-- | `Evals` with one entry per chunk, before the Horner recombination
-- | `Pickles.PlonkChecks.collapseChunkedEvals` performs. At
-- | `num_chunks = 1` every array has length 1 and that collapse is the
-- | identity.
type ChunkedEvals a =
  { publicEvals :: NonEmptyArray (PointEval a)
  , witnessEvals :: Vector 15 (NonEmptyArray (PointEval a))
  , coeffEvals :: Vector 15 (NonEmptyArray (PointEval a))
  , zEvals :: NonEmptyArray (PointEval a)
  , sigmaEvals :: Vector 6 (NonEmptyArray (PointEval a))
  , indexEvals :: Vector 6 (NonEmptyArray (PointEval a))
  , ftEval1 :: a
  }

-- | `Evals` in allocatable form. The newtype exists only to carry the
-- | `CircuitType`/`CheckedType` instances away from `RCircuitType`'s
-- | alphabetical field order: the wire order is `(public, witness,
-- | coefficients, z, sigma, index, ftEval1)`, spelled out in the
-- | `Tuple7`/`Tuple2` below and nowhere else.
newtype AllocEvals a = AllocEvals (Evals a)

-- | One evaluation as the ordered pair the wire wants: `zeta` first,
-- | then `omega*zeta`. The record alphabetizes them the other way
-- | round, so every crossing of this boundary goes through `evalPair` /
-- | `pairEval`.
evalPair :: forall a. PointEval a -> Tuple2 a a
evalPair p = tuple2 p.zeta p.omegaTimesZeta

pairEval :: forall a. Tuple2 a a -> PointEval a
pairEval = uncurry2 \zeta omegaTimesZeta -> { zeta, omegaTimesZeta }

-- | The seven blocks in wire order; with `evalPair` this is the whole
-- | wire layout of an `Evals`.
type EvalsTuple a =
  Tuple7 (Tuple2 a a) (Vector 15 (Tuple2 a a)) (Vector 15 (Tuple2 a a)) (Tuple2 a a)
    (Vector 6 (Tuple2 a a))
    (Vector 6 (Tuple2 a a))
    a

evalsTuple :: forall a. Evals a -> EvalsTuple a
evalsTuple r = tuple7 (evalPair r.publicEvals) (map evalPair r.witnessEvals)
  (map evalPair r.coeffEvals)
  (evalPair r.zEvals)
  (map evalPair r.sigmaEvals)
  (map evalPair r.indexEvals)
  r.ftEval1

tupleEvals :: forall a. EvalsTuple a -> AllocEvals a
tupleEvals = uncurry7
  \publicEvals witnessEvals coeffEvals zEvals sigmaEvals indexEvals ftEval1 -> AllocEvals
    { publicEvals: pairEval publicEvals
    , witnessEvals: map pairEval witnessEvals
    , coeffEvals: map pairEval coeffEvals
    , zEvals: pairEval zEvals
    , sigmaEvals: map pairEval sigmaEvals
    , indexEvals: map pairEval indexEvals
    , ftEval1
    }

instance (CircuitType f a var) => CircuitType f (AllocEvals a) (AllocEvals var) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(EvalsTuple a))
  valueToFields (AllocEvals r) = genericValueToFields (evalsTuple r)
  fieldsToValue fs = tupleEvals (genericFieldsToValue fs :: EvalsTuple a)
  varToFields (AllocEvals r) = genericVarToFields @(EvalsTuple a) (evalsTuple r)
  fieldsToVar fs = tupleEvals (genericFieldsToVar @(EvalsTuple a) fs :: EvalsTuple var)

instance (CheckedType f c var) => CheckedType f c (AllocEvals var) where
  check (AllocEvals r) = check (evalsTuple r)

-- | One prev proof's unfinalized deferred values, as allocated into the
-- | step statement's public input. The fields are written in wire
-- | order, which the `Tuple2` split below pins.
-- |
-- | The `UnChecked (SizedF 128 f)` fields are claimed to be 128 bits
-- | but are not range-checked at allocation.
newtype PerProofUnfinalized (d :: Int) sf f b = PerProofUnfinalized
  { combinedInnerProduct :: sf
  , b :: sf
  , zetaToSrsLength :: sf
  , zetaToDomainSize :: sf
  , perm :: sf
  , spongeDigest :: f
  , beta :: UnChecked (SizedF 128 f)
  , gamma :: UnChecked (SizedF 128 f)
  , alpha :: UnChecked (SizedF 128 f)
  , zeta :: UnChecked (SizedF 128 f)
  , xi :: UnChecked (SizedF 128 f)
  , bulletproofChallenges :: Vector d (UnChecked (SizedF 128 f))
  , shouldFinalize :: b
  }

-- | `PerProofUnfinalized`'s wire layout. Its 13 fields exceed
-- | `Tuple10`, the widest nested tuple, so they are carried as a
-- | 10 + 3 split.
type PerProofUnfinalizedTuple d sf x b =
  Tuple2
    (Tuple10 sf sf sf sf sf x (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)))
    (Tuple3 (UnChecked (SizedF 128 x)) (Vector d (UnChecked (SizedF 128 x))) b)

instance
  ( CircuitType f sf sfvar
  , CircuitType f b bvar
  , FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f (PerProofUnfinalized d sf (F f) b) (PerProofUnfinalized d sfvar (FVar f) bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PerProofUnfinalizedTuple d sf (F f) b))
  valueToFields (PerProofUnfinalized r) = genericValueToFields
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple3 r.xi r.bulletproofChallenges r.shouldFinalize)
    )
  fieldsToValue fs =
    let
      tup :: PerProofUnfinalizedTuple d sf (F f) b
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \t10 t3 ->
            uncurry10
              ( \cip bb zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry3
                    ( \xi bulletproofChallenges shouldFinalize ->
                        PerProofUnfinalized { combinedInnerProduct: cip, b: bb, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges, shouldFinalize }
                    )
                    t3
              )
              t10
        )
        tup
  varToFields (PerProofUnfinalized r) = genericVarToFields
    @(PerProofUnfinalizedTuple d sf (F f) b)
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple3 r.xi r.bulletproofChallenges r.shouldFinalize)
    )
  fieldsToVar fs =
    let
      tup :: PerProofUnfinalizedTuple d sfvar (FVar f) bvar
      tup = genericFieldsToVar @(PerProofUnfinalizedTuple d sf (F f) b) fs
    in
      uncurry2
        ( \t10 t3 ->
            uncurry10
              ( \cip bb zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry3
                    ( \xi bulletproofChallenges shouldFinalize ->
                        PerProofUnfinalized { combinedInnerProduct: cip, b: bb, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges, shouldFinalize }
                    )
                    t3
              )
              t10
        )
        tup

instance
  ( CheckedType f c sfvar
  , CheckedType f c fvar
  , CheckedType f c bvar
  ) =>
  CheckedType f c (PerProofUnfinalized d sfvar fvar bvar) where
  check (PerProofUnfinalized r) = check
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple3 r.xi r.bulletproofChallenges r.shouldFinalize)
    )

