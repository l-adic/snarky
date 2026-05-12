-- | Pickles-specific type aliases for the Pasta 2-cycle.
-- |
-- | Centralizes f types, IPA round counts, commitment curve aliases,
-- | and Step circuit I/O types used throughout the Pickles modules and tests.
-- |
-- | Reference: mina/src/lib/pickles/common/nat.ml, kimchi_pasta_basic.ml
module Pickles.Types
  ( StepIPARounds
  , WrapIPARounds
  , MaxProofsVerified
  , PaddedLength
  , StepCommitmentCurve
  , WrapCommitmentCurve
  , StepInput
  , StepStatement
  , WrapStatement
  , PointEval(..)
  , StatementIO(..)
  , WrapProofMessages(..)
  , WrapProofOpening(..)
  , StepAllEvals(..)
  , PerProofUnfinalized(..)
  ) where

import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple5, Tuple7, tuple10, tuple2, tuple3, tuple5, tuple7, uncurry10, uncurry2, uncurry3, uncurry5, uncurry7)
import Data.Vector (Vector)
import Pickles.Verify.Types (UnfinalizedProof, WrapDeferredValues)
import Snarky.Circuit.DSL (F, FVar, UnChecked)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
type StepIPARounds = 16

-- | IPA rounds in a Wrap proof (= log2 of Pallas SRS size = Rounds.Wrap = 15).
type WrapIPARounds = 15

-- | Maximum number of previous proofs verified per step. In Pickles
-- | this is the **per-compile-circuit** `max_proofs_verified` parameter
-- | — OCaml supports N0, N1, or N2 per circuit (see `pickles.ml`
-- | compile sites and `wrap_main.ml`'s locally-abstract type). The
-- | current PS port still hardcodes the 2 case, but this alias exists
-- | as the handle that will become an `mpv` type variable when
-- | `wrap_main` is polymorphized.
-- |
-- | DO NOT confuse with `PaddedLength` below — they're numerically
-- | equal in the N2 instantiation but semantically distinct.
-- |
-- | Reference: mina/src/lib/pickles/common/nat.ml (N0 | N1 | N2)
type MaxProofsVerified = 2

-- | Universal `Wrap_hack.Padded_length`. Defined in
-- | `wrap_hack.ml:24` as `module Padded_length = Nat.N2` — a
-- | compile-time constant of 2, unrelated to any particular circuit's
-- | `max_proofs_verified`. Used as the padding target for each slot's
-- | bp-challenge vector (`Wrap_hack.Checked.pad_challenges`), for the
-- | wrap proof's `sg` list in `Step_main`'s `sgOld`, and as the ceiling
-- | on `Proofs_verified.Prefix_mask` length (`proofs_verified.ml:70`).
-- |
-- | The pre-computed `dummyPaddingSpongeStates` table has exactly
-- | `PaddedLength + 1 = 3` entries (for absorbing 0, 1, or 2 dummies).
-- |
-- | This is a UNIVERSAL constant across Pickles — it does **not**
-- | vary with `max_proofs_verified`.
-- |
-- | Reference: mina/src/lib/pickles/wrap_hack.ml:24
type PaddedLength = 2

-- | Step proofs commit on Vesta (scalar f = Fp = StepField).
type StepCommitmentCurve = Vesta.G

-- | Wrap proofs commit on Pallas (scalar f = Fq = WrapField).
type WrapCommitmentCurve = Pallas.G

-------------------------------------------------------------------------------
-- | Step Circuit I/O Types
-------------------------------------------------------------------------------

-- | Input to the Step circuit combinator.
-- |
-- | Bundles the application input with the proof witness data.
-- |
-- | Parameters:
-- | - `n`: Number of previous proofs to verify
-- | - `input`: Application-specific input type
-- | - `prevInput`: Previous proof public input type
-- | - `ds`: Step IPA rounds (phantom, carried for type bookkeeping)
-- | - `dw`: Wrap IPA rounds (used: previous Wrap proofs have dw bulletproof challenges)
-- | - `f`: Field element type
-- | - `sf`: Shifted scalar type
-- | - `b`: Boolean type
type StepInput :: Int -> Type -> Type -> Int -> Int -> Type -> Type -> Type -> Type
type StepInput n input prevInput ds dw f sf b =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  , unfinalizedProofs :: Vector n (UnfinalizedProof dw f sf b)
  , prevChallengeDigests :: Vector n f
  }

-- | The Step circuit's output statement.
-- |
-- | This becomes part of the public input for the Wrap circuit to verify.
-- |
-- | The `fv` parameter is the f variable type (e.g., `FVar f` in circuits).
-- | The `sf` parameter is the shifted value type (e.g., `Type1 (FVar f)`).
-- | The `b` parameter is the boolean type (e.g., `BoolVar f`).
-- |
-- | Reference: step_main.ml:587-594 `Types.Step.Statement`
type StepStatement :: Int -> Int -> Int -> Type -> Type -> Type -> Type
type StepStatement n ds dw fv sf b =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv sf b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-------------------------------------------------------------------------------
-- | Wrap Circuit I/O Types
-------------------------------------------------------------------------------

-- | The Wrap circuit's public input statement.
-- |
-- | Contains Wrap deferred values (with branch_data) + message digests.
-- | This is what the Step circuit packs via Spec.pack for x_hat.
-- |
-- | The `b` parameter is the boolean type (Boolean for values, BoolVar for circuit).
-- |
-- | Reference: Wrap.Statement.In_circuit.t (composition_types.ml:623-658)
type WrapStatement :: Int -> Type -> Type -> Type -> Type
type WrapStatement d f sf b =
  { proofState ::
      { deferredValues :: WrapDeferredValues d f sf b
      , spongeDigestBeforeEvaluations :: f
      , messagesForNextWrapProof :: f
      }
  , messagesForNextStepProof :: f
  }

-------------------------------------------------------------------------------
-- | Building blocks for structured witness allocation
-- |
-- | These newtypes wrap records but their `CircuitType`/`CheckedType`
-- | instances delegate to an internal nested-`Tuple` representation that
-- | enforces OCaml's exact allocation order (instead of the alphabetical
-- | RowList order a record would give).
-- |
-- | Parameterized by a single element type so the same newtype works for
-- | both value (`F f`) and var (`FVar f`) representations.
-------------------------------------------------------------------------------

-- | A polynomial evaluation at the pair (zeta, zeta*omega).
-- |
-- | OCaml pairs are allocated as `(zeta_eval, omega_eval)` — zeta FIRST,
-- | then omega*zeta. A plain record `{zeta, omegaTimesZeta}` would
-- | alphabetize to (omegaTimesZeta, zeta) via RowList, which is WRONG.
-- | This newtype enforces OCaml order via nested-Tuple delegation.
newtype PointEval a = PointEval
  { zeta :: a
  , omegaTimesZeta :: a
  }

instance (CircuitType f a var) => CircuitType f (PointEval a) (PointEval var) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple2 a a))
  valueToFields (PointEval r) = genericValueToFields (tuple2 r.zeta r.omegaTimesZeta)
  fieldsToValue fs =
    let
      tup :: Tuple2 a a
      tup = genericFieldsToValue fs
    in
      uncurry2 (\zeta omegaTimesZeta -> PointEval { zeta, omegaTimesZeta }) tup
  varToFields (PointEval r) = genericVarToFields @(Tuple2 a a) (tuple2 r.zeta r.omegaTimesZeta)
  fieldsToVar fs =
    let
      tup :: Tuple2 var var
      tup = genericFieldsToVar @(Tuple2 a a) fs
    in
      uncurry2 (\zeta omegaTimesZeta -> PointEval { zeta, omegaTimesZeta }) tup

instance (CheckedType f c var) => CheckedType f c (PointEval var) where
  check (PointEval r) = check (tuple2 r.zeta r.omegaTimesZeta)

-- | The statement (public input to kimchi verify) of a Pickles rule.
-- |
-- | Every rule's statement has at most two components: its main-function
-- | `input` and its returned `output`. Existing Pickles tests use three
-- | public-input modes (`Input typ`, `Output typ`, `Input_and_output`)
-- | captured uniformly by this single shape:
-- |
-- |   Input typ             → StatementIO input Unit
-- |   Output typ            → StatementIO Unit output
-- |   Input_and_output i o  → StatementIO i o
-- |
-- | `CircuitType Unit Unit` serializes to zero fields, so the "unused"
-- | side contributes no field elements to the kimchi public-input array.
-- | The byte layout matches OCaml's current conventions for all three
-- | modes without special-casing.
-- |
-- | Field order is `input` first, then `output` — matches OCaml's
-- | `Input_and_output` tuple convention. Record fields alphabetize via
-- | RowList to the same order here since `input` < `output`; we still
-- | route through explicit `Tuple2` to make the ordering contract visible
-- | at the type-class-instance site.
newtype StatementIO input output = StatementIO
  { input :: input
  , output :: output
  }

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

-- | Wrap proof messages: protocol commitments allocated in the per-proof witness.
-- |
-- | OCaml hlist order: w_comm (15), z_comm (1), t_comm (7).
-- | Reference: kimchi_types.ml prover_proof.commitments
-- |
-- | Carries `n :: Int = num_chunks` (`docs/chunking.md`). At n=1 every
-- | inner `Vector n` collapses to a singleton, which is byte-equivalent
-- | to the pre-chunking flat shapes (Vector 15 pt / pt / Vector 7 pt).
-- |   * `wComm` — 15 polynomials × n chunks each.
-- |   * `zComm` — 1 polynomial with n chunks.
-- |   * `tComm` — quotient poly's 7-chunk overhead, each sub-split into
-- |     n chunks (total `7 * n` group elements). Nested for type clarity;
-- |     CircuitType flattens to a single 7n-long vector.
newtype WrapProofMessages :: Int -> Type -> Type
newtype WrapProofMessages n pt = WrapProofMessages
  { wComm :: Vector 15 (Vector n pt)
  , zComm :: Vector n pt
  , tComm :: Vector 7 (Vector n pt)
  }

instance
  ( CircuitType f a var
  , Reflectable n Int
  ) =>
  CircuitType f (WrapProofMessages n a) (WrapProofMessages n var) where
  sizeInFields pf _ =
    genericSizeInFields pf (Proxy @(Tuple3 (Vector 15 (Vector n a)) (Vector n a) (Vector 7 (Vector n a))))
  valueToFields (WrapProofMessages r) = genericValueToFields (tuple3 r.wComm r.zComm r.tComm)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 15 (Vector n a)) (Vector n a) (Vector 7 (Vector n a))
      tup = genericFieldsToValue fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup
  varToFields (WrapProofMessages r) =
    genericVarToFields @(Tuple3 (Vector 15 (Vector n a)) (Vector n a) (Vector 7 (Vector n a))) (tuple3 r.wComm r.zComm r.tComm)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 15 (Vector n var)) (Vector n var) (Vector 7 (Vector n var))
      tup = genericFieldsToVar @(Tuple3 (Vector 15 (Vector n a)) (Vector n a) (Vector 7 (Vector n a))) fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup

instance (CheckedType f c var) => CheckedType f c (WrapProofMessages n var) where
  check (WrapProofMessages r) = check (tuple3 r.wComm r.zComm r.tComm)

-- | Wrap proof opening: bulletproof opening data allocated in the per-proof witness.
-- |
-- | OCaml hlist order: lr (Vector n {l, r}), z1, z2, delta, sg.
-- | Reference: kimchi_types.ml opening_proof
-- |
-- | The `n` parameter is the IPA rounds count. For openings VERIFYING a step
-- | proof inside the wrap circuit, `n = StepIPARounds = 16`. For openings
-- | VERIFYING a wrap proof inside the step circuit, `n = WrapIPARounds = 15`.
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

-- | All polynomial evaluations for the wrap proof being verified.
-- |
-- | OCaml hlist order: public_input, witness (15), coefficients (15), z, sigma (6),
-- | index_evals (6 selectors), ft_eval1.
-- |
-- | Each evaluation is a `PointEval` (zeta, omega*zeta) — the `PointEval` newtype
-- | enforces zeta-first ordering.
newtype StepAllEvals a = StepAllEvals
  { publicEvals :: PointEval a
  , witnessEvals :: Vector 15 (PointEval a)
  , coeffEvals :: Vector 15 (PointEval a)
  , zEvals :: PointEval a
  , sigmaEvals :: Vector 6 (PointEval a)
  , indexEvals :: Vector 6 (PointEval a)
  , ftEval1 :: a
  }

instance (CircuitType f a var) => CircuitType f (StepAllEvals a) (StepAllEvals var) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple7 (PointEval a) (Vector 15 (PointEval a)) (Vector 15 (PointEval a)) (PointEval a) (Vector 6 (PointEval a)) (Vector 6 (PointEval a)) a))
  valueToFields (StepAllEvals r) = genericValueToFields
    (tuple7 r.publicEvals r.witnessEvals r.coeffEvals r.zEvals r.sigmaEvals r.indexEvals r.ftEval1)
  fieldsToValue fs =
    let
      tup :: Tuple7 (PointEval a) (Vector 15 (PointEval a)) (Vector 15 (PointEval a)) (PointEval a) (Vector 6 (PointEval a)) (Vector 6 (PointEval a)) a
      tup = genericFieldsToValue fs
    in
      uncurry7
        ( \publicEvals witnessEvals coeffEvals zEvals sigmaEvals indexEvals ftEval1 ->
            StepAllEvals { publicEvals, witnessEvals, coeffEvals, zEvals, sigmaEvals, indexEvals, ftEval1 }
        )
        tup
  varToFields (StepAllEvals r) = genericVarToFields
    @(Tuple7 (PointEval a) (Vector 15 (PointEval a)) (Vector 15 (PointEval a)) (PointEval a) (Vector 6 (PointEval a)) (Vector 6 (PointEval a)) a)
    (tuple7 r.publicEvals r.witnessEvals r.coeffEvals r.zEvals r.sigmaEvals r.indexEvals r.ftEval1)
  fieldsToVar fs =
    let
      tup :: Tuple7 (PointEval var) (Vector 15 (PointEval var)) (Vector 15 (PointEval var)) (PointEval var) (Vector 6 (PointEval var)) (Vector 6 (PointEval var)) var
      tup =
        genericFieldsToVar
          @(Tuple7 (PointEval a) (Vector 15 (PointEval a)) (Vector 15 (PointEval a)) (PointEval a) (Vector 6 (PointEval a)) (Vector 6 (PointEval a)) a)
          fs
    in
      uncurry7
        ( \publicEvals witnessEvals coeffEvals zEvals sigmaEvals indexEvals ftEval1 ->
            StepAllEvals { publicEvals, witnessEvals, coeffEvals, zEvals, sigmaEvals, indexEvals, ftEval1 }
        )
        tup

instance (CheckedType f c var) => CheckedType f c (StepAllEvals var) where
  check (StepAllEvals r) = check (tuple7 r.publicEvals r.witnessEvals r.coeffEvals r.zEvals r.sigmaEvals r.indexEvals r.ftEval1)

-- | Per-proof unfinalized proof: the OCaml `Unfinalized.t` allocation that
-- | becomes part of the Step.Statement public input.
-- |
-- | OCaml to_data order:
-- |   cip, b, zetaToSrs, zetaToDom, perm,    -- 5 shifted fields (Type2 in step)
-- |   spongeDigest,                          -- digest (plain f)
-- |   beta, gamma,                           -- 2 128-bit challenges
-- |   alpha, zeta, xi,                       -- 3 128-bit scalar challenges
-- |   bulletproofChallenges,                 -- Vector d of 128-bit challenges
-- |   shouldFinalize                         -- bool
-- |
-- | The `UnChecked (SizedF 128 f)` fields are claimed-128-bit but NOT range-checked
-- | at allocation (matching OCaml's `Challenge.typ = Typ.f`).
-- |
-- | Type parameters:
-- | - `d`: number of bulletproof challenges
-- | - `sf`: shifted-f type (e.g., `Type2 (SplitField (F f) Boolean)`)
-- | - `f`: plain f type
-- | - `b`: boolean type
-- |
-- | Reference: unfinalized.ml
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

-- | Tuple shape for PerProofUnfinalized, parameterized by:
-- |   - sf: shifted-f type (sf or sfvar)
-- |   - x:  field element type (F f or FVar f)
-- |   - b:  boolean type (b or bvar)
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

