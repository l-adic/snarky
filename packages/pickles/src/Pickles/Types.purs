-- | Pickles-specific type aliases for the Pasta 2-cycle.
-- |
-- | Centralizes f types, IPA round counts, commitment curve aliases,
-- | and Step circuit I/O types used throughout the Pickles modules and tests.
-- |
-- | Reference: mina/src/lib/pickles/common/nat.ml, kimchi_pasta_basic.ml
module Pickles.Types
  ( StepField
  , WrapField
  , StepIPARounds
  , WrapIPARounds
  , MaxProofsVerified
  , StepCommitmentCurve
  , WrapCommitmentCurve
  , StepInput
  , StepStatement
  , WrapStatement
  , PointEval(..)
  , VerificationKey(..)
  , BranchData(..)
  , WrapProofMessages(..)
  , WrapProofOpening(..)
  , WrapProof(..)
  , StepAllEvals(..)
  , FopProofState(..)
  , StepProofState(..)
  , StepPerProofWitness(..)
  , PerProofUnfinalized(..)
  , WrapPrevProofState(..)
  , WrapOldBpChals(..)
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple5, Tuple7, tuple10, tuple2, tuple3, tuple5, tuple7, uncurry10, uncurry2, uncurry3, uncurry5, uncurry7)
import Data.Vector (Vector)
import Partial.Unsafe (unsafePartial)
import Pickles.Verify.Types (UnfinalizedProof, WrapDeferredValues)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (BoolVar, F, FVar, UnChecked, const_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, EndoScalar(..), endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Type.Proxy (Proxy(..))

-- | Step circuit f (Fp = Vesta.ScalarField = Pallas.BaseField).
type StepField = Vesta.ScalarField

-- | Wrap circuit f (Fq = Pallas.ScalarField = Vesta.BaseField).
type WrapField = Pallas.ScalarField

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
type StepIPARounds = 16

-- | IPA rounds in a Wrap proof (= log2 of Pallas SRS size = Rounds.Wrap = 15).
type WrapIPARounds = 15

-- | Maximum number of previous proofs verified per step (always 2 in Pickles).
-- | Reference: mina/src/lib/pickles/common/nat.ml (N2)
type MaxProofsVerified = 2

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

-- | Plonk verification key: sigma(7), coefficients(15), index(6) commitments.
-- |
-- | OCaml hlist order: sigma_comm, coefficients_comm, index commitments
-- | (generic, psm, complete_add, mul, emul, endomul_scalar).
-- |
-- | Parameterized by the element type so the same newtype works for both
-- | value and var representations on either Pasta curve.
-- |
-- | Reference: plonk_verification_key_evals.ml
newtype VerificationKey pt = VerificationKey
  { sigma :: Vector 7 pt
  , coeff :: Vector 15 pt
  , index :: Vector 6 pt
  }

instance (CircuitType f a var) => CircuitType f (VerificationKey a) (VerificationKey var) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)))
  valueToFields (VerificationKey r) = genericValueToFields (tuple3 r.sigma r.coeff r.index)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)
      tup = genericFieldsToValue fs
    in
      uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup
  varToFields (VerificationKey r) = genericVarToFields @(Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)) (tuple3 r.sigma r.coeff r.index)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 7 var) (Vector 15 var) (Vector 6 var)
      tup = genericFieldsToVar @(Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)) fs
    in
      uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup

instance (CheckedType f c var) => CheckedType f c (VerificationKey var) where
  check (VerificationKey r) = check (tuple3 r.sigma r.coeff r.index)

-- | Per-proof branch data: which previous proof slot is in use, plus the
-- | wrap proof's domain log2.
-- |
-- | OCaml hlist order: (mask0, mask1, domainLog2). Allocation order matches
-- | the OCaml `Branch_data.typ`.
-- |
-- | The `CheckedType` instance:
-- | - Boolean checks on the masks (via Tuple3 delegation to inner instances)
-- | - Endoscalar check on `domainLog2` (matching OCaml's
-- |   `Branch_data.typ.check`, which expands the 16-bit log2 into a full
-- |   f element through the endo).
-- |
-- | The endo constant is determined by `f` via the `HasEndo` class — for
-- | `f = StepField` (= Vesta.ScalarField), the base f is Vesta.BaseField
-- | and `endoScalar @Vesta.BaseField @StepField` gives the right value.
-- |
-- | Reference: branch_data.ml, mina/src/lib/crypto/pickles/impls.ml
newtype BranchData f b = BranchData
  { mask0 :: b
  , mask1 :: b
  , domainLog2 :: f
  }

instance
  ( CircuitType f a fvar
  , CircuitType f b bvar
  ) =>
  CircuitType f (BranchData a b) (BranchData fvar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple3 b b a))
  valueToFields (BranchData r) = genericValueToFields (tuple3 r.mask0 r.mask1 r.domainLog2)
  fieldsToValue fs =
    let
      tup :: Tuple3 b b a
      tup = genericFieldsToValue fs
    in
      uncurry3 (\mask0 mask1 domainLog2 -> BranchData { mask0, mask1, domainLog2 }) tup
  varToFields (BranchData r) = genericVarToFields @(Tuple3 b b a) (tuple3 r.mask0 r.mask1 r.domainLog2)
  fieldsToVar fs =
    let
      tup :: Tuple3 bvar bvar fvar
      tup = genericFieldsToVar @(Tuple3 b b a) fs
    in
      uncurry3 (\mask0 mask1 domainLog2 -> BranchData { mask0, mask1, domainLog2 }) tup

-- | CheckedType for the var representation: Boolean checks on the masks
-- | plus the endoscalar check on domainLog2.
instance
  ( FieldSizeInBits f n
  , Compare 16 n LT
  , HasEndo basef f
  , CheckedType f (KimchiConstraint f) (Tuple3 (BoolVar f) (BoolVar f) (FVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (BranchData (FVar f) (BoolVar f)) where
  check (BranchData r) = label "branch-data-check" do
    -- Boolean checks on masks + (no-op) check on domLog2 via Tuple3 delegation
    check (tuple3 r.mask0 r.mask1 r.domainLog2)
    -- Endoscalar check on domainLog2 (matches OCaml Branch_data.typ.check)
    let EndoScalar e = endoScalar @basef @f
    _ <- EndoScalar.toField @1 (unsafePartial (unsafeFromField r.domainLog2) :: SizedF 16 (FVar f)) (const_ e)
    pure unit

-- | Wrap proof messages: protocol commitments allocated in the per-proof witness.
-- |
-- | OCaml hlist order: w_comm (15), z_comm (1), t_comm (7).
-- | Reference: kimchi_types.ml prover_proof.commitments
newtype WrapProofMessages pt = WrapProofMessages
  { wComm :: Vector 15 pt
  , zComm :: pt
  , tComm :: Vector 7 pt
  }

instance (CircuitType f a var) => CircuitType f (WrapProofMessages a) (WrapProofMessages var) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple3 (Vector 15 a) a (Vector 7 a)))
  valueToFields (WrapProofMessages r) = genericValueToFields (tuple3 r.wComm r.zComm r.tComm)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 15 a) a (Vector 7 a)
      tup = genericFieldsToValue fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup
  varToFields (WrapProofMessages r) = genericVarToFields @(Tuple3 (Vector 15 a) a (Vector 7 a)) (tuple3 r.wComm r.zComm r.tComm)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 15 var) var (Vector 7 var)
      tup = genericFieldsToVar @(Tuple3 (Vector 15 a) a (Vector 7 a)) fs
    in
      uncurry3 (\wComm zComm tComm -> WrapProofMessages { wComm, zComm, tComm }) tup

instance (CheckedType f c var) => CheckedType f c (WrapProofMessages var) where
  check (WrapProofMessages r) = check (tuple3 r.wComm r.zComm r.tComm)

-- | Wrap proof opening: bulletproof opening data allocated in the per-proof witness.
-- |
-- | OCaml hlist order: lr (Vector d {l, r}), z1, z2, delta, sg.
-- | Reference: kimchi_types.ml opening_proof
newtype WrapProofOpening pt sf = WrapProofOpening
  { lr :: Vector 15 { l :: pt, r :: pt }
  , z1 :: sf
  , z2 :: sf
  , delta :: pt
  , sg :: pt
  }

instance
  ( CircuitType f a avar
  , CircuitType f b bvar
  ) =>
  CircuitType f (WrapProofOpening a b) (WrapProofOpening avar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple5 (Vector 15 { l :: a, r :: a }) b b a a))
  valueToFields (WrapProofOpening r) = genericValueToFields (tuple5 r.lr r.z1 r.z2 r.delta r.sg)
  fieldsToValue fs =
    let
      tup :: Tuple5 (Vector 15 { l :: a, r :: a }) b b a a
      tup = genericFieldsToValue fs
    in
      uncurry5 (\lr z1 z2 delta sg -> WrapProofOpening { lr, z1, z2, delta, sg }) tup
  varToFields (WrapProofOpening r) = genericVarToFields @(Tuple5 (Vector 15 { l :: a, r :: a }) b b a a) (tuple5 r.lr r.z1 r.z2 r.delta r.sg)
  fieldsToVar fs =
    let
      tup :: Tuple5 (Vector 15 { l :: avar, r :: avar }) bvar bvar avar avar
      tup = genericFieldsToVar @(Tuple5 (Vector 15 { l :: a, r :: a }) b b a a) fs
    in
      uncurry5 (\lr z1 z2 delta sg -> WrapProofOpening { lr, z1, z2, delta, sg }) tup

instance
  ( CheckedType f c avar
  , CheckedType f c bvar
  ) =>
  CheckedType f c (WrapProofOpening avar bvar) where
  check (WrapProofOpening r) = check (tuple5 r.lr r.z1 r.z2 r.delta r.sg)

-- | Combined wrap proof: messages + opening, in OCaml's `Wrap_proof.Checked.t` order.
-- |
-- | Reference: wrap_proof.ml — `{ messages; opening }` allocated via
-- | `of_hlistable` which gives field order (messages first, then opening).
newtype WrapProof pt sf = WrapProof
  { messages :: WrapProofMessages pt
  , opening :: WrapProofOpening pt sf
  }

instance
  ( CircuitType f a avar
  , CircuitType f b bvar
  ) =>
  CircuitType f (WrapProof a b) (WrapProof avar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple2 (WrapProofMessages a) (WrapProofOpening a b)))
  valueToFields (WrapProof r) = genericValueToFields (tuple2 r.messages r.opening)
  fieldsToValue fs =
    let
      tup :: Tuple2 (WrapProofMessages a) (WrapProofOpening a b)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup
  varToFields (WrapProof r) = genericVarToFields @(Tuple2 (WrapProofMessages a) (WrapProofOpening a b)) (tuple2 r.messages r.opening)
  fieldsToVar fs =
    let
      tup :: Tuple2 (WrapProofMessages avar) (WrapProofOpening avar bvar)
      tup = genericFieldsToVar @(Tuple2 (WrapProofMessages a) (WrapProofOpening a b)) fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup

instance
  ( CheckedType f c avar
  , CheckedType f c bvar
  ) =>
  CheckedType f c (WrapProof avar bvar) where
  check (WrapProof r) = check (tuple2 r.messages r.opening)

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

-- | FOP proof state: deferred values + sponge digest, in OCaml's to_data order.
-- |
-- | OCaml to_data order (from `Spec.pack` of `Per_proof_witness.proof_state`):
-- |   cip, b, zetaToSrs, zetaToDom, perm,    -- 5 plain fields (Type1 in step)
-- |   spongeDigest,                          -- digest (plain f)
-- |   beta, gamma,                           -- 2 128-bit challenges
-- |   alpha, zeta, xi,                       -- 3 128-bit scalar challenges
-- |   bulletproofChallenges                  -- Vector d of 128-bit challenges
-- |
-- | The `UnChecked (SizedF 128 f)` fields are claimed-128-bit but NOT range-checked
-- | at allocation (matching OCaml's `Challenge.typ = Typ.f`). Use
-- | `challengeToSizedF` at the boundary with FOP/IVP code that needs
-- | `SizedF 128 f`.
-- |
-- | Note: the `branchData` is allocated separately within the per-proof witness;
-- | it is NOT part of this newtype.
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

-- | Tuple shape for FopProofState (parameterized by element type x).
-- | Used by both value (x = F f) and var (x = FVar f) instances.
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

-- | Step proof state: deferred values + sponge digest + branch data, in
-- | the OCaml allocation order from `Wrap.Proof_state.In_circuit`'s
-- | `Spec.packed_typ` flattening.
-- |
-- | The to_data order puts the FopProofState fields first (cip, b, zetaToSrs,
-- | zetaToDom, perm, sponge, beta, gamma, alpha, zeta, xi, bpChals), then
-- | branchData (mask0, mask1, domLog2 with endoscalar check) at the end.
-- |
-- | Reference: composition_types.ml `Wrap.Proof_state` allocation
newtype StepProofState f b = StepProofState
  { fopState :: FopProofState StepIPARounds f
  , branchData :: BranchData f b
  }

instance
  ( FieldSizeInBits f m
  ) =>
  CircuitType f (StepProofState (F f) Boolean) (StepProofState (FVar f) (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (FopProofState StepIPARounds (F f)) (BranchData (F f) Boolean)))
  valueToFields (StepProofState r) = genericValueToFields (tuple2 r.fopState r.branchData)
  fieldsToValue fs =
    let
      tup :: Tuple2 (FopProofState StepIPARounds (F f)) (BranchData (F f) Boolean)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\fopState branchData -> StepProofState { fopState, branchData }) tup
  varToFields (StepProofState r) = genericVarToFields
    @(Tuple2 (FopProofState StepIPARounds (F f)) (BranchData (F f) Boolean))
    (tuple2 r.fopState r.branchData)
  fieldsToVar fs =
    let
      tup :: Tuple2 (FopProofState StepIPARounds (FVar f)) (BranchData (FVar f) (BoolVar f))
      tup = genericFieldsToVar @(Tuple2 (FopProofState StepIPARounds (F f)) (BranchData (F f) Boolean)) fs
    in
      uncurry2 (\fopState branchData -> StepProofState { fopState, branchData }) tup

instance
  ( CheckedType f (KimchiConstraint f) (FopProofState StepIPARounds (FVar f))
  , CheckedType f (KimchiConstraint f) (BranchData (FVar f) (BoolVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (StepProofState (FVar f) (BoolVar f)) where
  check (StepProofState r) = check (tuple2 r.fopState r.branchData)

-- | Composed per-proof witness: the OCaml `Per_proof_witness.No_app_state.t`.
-- |
-- | OCaml hlist order (5 components after dropping the Unit statement):
-- |   1. wrap_proof  : Wrap_proof.Checked.t      (messages + opening)
-- |   2. proof_state : Wrap.Proof_state.In_circuit.t  (deferred values + sponge_digest + branch_data, with msg_for_next_wrap=unit)
-- |   3. prev_proof_evals : All_evals.In_circuit.t
-- |   4. prev_challenges : (Vector field tick, max_proofs_verified) Vector
-- |   5. prev_challenge_polynomial_commitments : (inner_curve, max_proofs_verified) Vector
-- |
-- | This is one structured `exists` call in OCaml step_main:
-- |   `exists (Prev_typ.f prev_proof_typs) ~request:Req.Proof_with_datas`
-- |
-- | Reference: per_proof_witness.ml, step_main.ml
newtype StepPerProofWitness (n :: Int) f sf b = StepPerProofWitness
  { wrapProof :: WrapProof (WeierstrassAffinePoint PallasG f) sf
  , proofState :: StepProofState f b
  , prevEvals :: StepAllEvals f
  , prevChallenges :: Vector n (UnChecked (Vector StepIPARounds f))
  , prevSgs :: Vector n (WeierstrassAffinePoint PallasG f)
  }

-- | Tuple shape for StepPerProofWitness, parameterized by:
-- |   - x:  field element type (F f or FVar f)
-- |   - sf: shifted-f type
-- |   - b:  boolean type
type StepPerProofWitnessTuple n x sf b =
  Tuple5
    (WrapProof (WeierstrassAffinePoint PallasG x) sf)
    (StepProofState x b)
    (StepAllEvals x)
    (Vector n (UnChecked (Vector StepIPARounds x)))
    (Vector n (WeierstrassAffinePoint PallasG x))

instance
  ( FieldSizeInBits f m
  , CircuitType f sf sfvar
  , Reflectable n Int
  ) =>
  CircuitType f
    (StepPerProofWitness n (F f) sf Boolean)
    (StepPerProofWitness n (FVar f) sfvar (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(StepPerProofWitnessTuple n (F f) sf Boolean))
  valueToFields (StepPerProofWitness r) = genericValueToFields
    (tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs)
  fieldsToValue fs =
    let
      tup :: StepPerProofWitnessTuple n (F f) sf Boolean
      tup = genericFieldsToValue fs
    in
      uncurry5
        ( \wrapProof proofState prevEvals prevChallenges prevSgs ->
            StepPerProofWitness { wrapProof, proofState, prevEvals, prevChallenges, prevSgs }
        )
        tup
  varToFields (StepPerProofWitness r) = genericVarToFields
    @(StepPerProofWitnessTuple n (F f) sf Boolean)
    (tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs)
  fieldsToVar fs =
    let
      tup :: StepPerProofWitnessTuple n (FVar f) sfvar (BoolVar f)
      tup = genericFieldsToVar @(StepPerProofWitnessTuple n (F f) sf Boolean) fs
    in
      uncurry5
        ( \wrapProof proofState prevEvals prevChallenges prevSgs ->
            StepPerProofWitness { wrapProof, proofState, prevEvals, prevChallenges, prevSgs }
        )
        tup

instance
  ( CheckedType StepField (KimchiConstraint StepField) (WrapProof (WeierstrassAffinePoint PallasG (FVar StepField)) sfvar)
  , CheckedType StepField (KimchiConstraint StepField) (StepProofState (FVar StepField) (BoolVar StepField))
  , CheckedType StepField (KimchiConstraint StepField) (StepAllEvals (FVar StepField))
  , Reflectable n Int
  ) =>
  CheckedType StepField (KimchiConstraint StepField) (StepPerProofWitness n (FVar StepField) sfvar (BoolVar StepField)) where
  check (StepPerProofWitness r) =
    let
      tup :: StepPerProofWitnessTuple n (FVar StepField) sfvar (BoolVar StepField)
      tup = tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs
    in
      check tup

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

-------------------------------------------------------------------------------
-- | Wrap circuit witness allocation types (used by Pickles.Wrap.Advice)
-------------------------------------------------------------------------------

-- | The combined wrap-circuit `Req.Proof_state` allocation: `mpv`
-- | unfinalized proofs (Type2-shifted scalars) + `messages_for_next_step_proof`.
-- |
-- | OCaml's `wrap_typ` over `Types.Step.Proof_state` puts `unfinalized_proofs`
-- | first (a Vector of length `mpv`) and `messages_for_next_step_proof` second.
-- |
-- | Reference: mina/src/lib/crypto/pickles/composition_types/composition_types.ml
-- | (`Types.Step.Proof_state.wrap_typ`) and `wrap_main.ml:267` exists call.
newtype WrapPrevProofState (mpv :: Int) sf f b = WrapPrevProofState
  { unfinalizedProofs :: Vector mpv (PerProofUnfinalized WrapIPARounds sf f b)
  , messagesForNextStepProof :: f
  }

instance
  ( CircuitType f sf sfvar
  , CircuitType f b bvar
  , FieldSizeInBits f m
  , Reflectable mpv Int
  ) =>
  CircuitType f
    (WrapPrevProofState mpv sf (F f) b)
    (WrapPrevProofState mpv sfvar (FVar f) bvar) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)))
  valueToFields (WrapPrevProofState r) = genericValueToFields
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToValue fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            WrapPrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup
  varToFields (WrapPrevProofState r) = genericVarToFields
    @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToVar fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sfvar (FVar f) bvar)) (FVar f)
      tup = genericFieldsToVar
        @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
        fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            WrapPrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup

instance
  ( CheckedType f c (Vector mpv (PerProofUnfinalized WrapIPARounds sfvar fvar bvar))
  , CheckedType f c fvar
  ) =>
  CheckedType f c (WrapPrevProofState mpv sfvar fvar bvar) where
  check (WrapPrevProofState r) = check (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)

-- | Old bulletproof challenges grouped by slot. The wrap circuit's
-- | `Req.Old_bulletproof_challenges` allocates a heterogeneous list over
-- | `Max_widths_by_slot.maxes`; for the configurations we currently dump,
-- | both slots are present but their widths can differ.
-- |
-- | OCaml's H1.Wrap_typ iterates head-to-tail over the maxes list, so slot 0
-- | is allocated first and slot 1 second.
-- |
-- | Type parameters:
-- | - `slot0Width`: number of bulletproof-challenge vectors in slot 0
-- | - `slot1Width`: number of bulletproof-challenge vectors in slot 1
-- | - `f`: field element type (`F f` or `FVar f`)
-- |
-- | Reference: wrap_main.ml:372-404 (`Req.Old_bulletproof_challenges`).
newtype WrapOldBpChals (slot0Width :: Int) (slot1Width :: Int) f = WrapOldBpChals
  { slot0 :: Vector slot0Width (Vector WrapIPARounds f)
  , slot1 :: Vector slot1Width (Vector WrapIPARounds f)
  }

instance
  ( CircuitType f a var
  , Reflectable slot0Width Int
  , Reflectable slot1Width Int
  ) =>
  CircuitType f (WrapOldBpChals slot0Width slot1Width a) (WrapOldBpChals slot0Width slot1Width var) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (Vector slot0Width (Vector WrapIPARounds a)) (Vector slot1Width (Vector WrapIPARounds a))))
  valueToFields (WrapOldBpChals r) = genericValueToFields (tuple2 r.slot0 r.slot1)
  fieldsToValue fs =
    let
      tup :: Tuple2 (Vector slot0Width (Vector WrapIPARounds a)) (Vector slot1Width (Vector WrapIPARounds a))
      tup = genericFieldsToValue fs
    in
      uncurry2 (\slot0 slot1 -> WrapOldBpChals { slot0, slot1 }) tup
  varToFields (WrapOldBpChals r) = genericVarToFields
    @(Tuple2 (Vector slot0Width (Vector WrapIPARounds a)) (Vector slot1Width (Vector WrapIPARounds a)))
    (tuple2 r.slot0 r.slot1)
  fieldsToVar fs =
    let
      tup :: Tuple2 (Vector slot0Width (Vector WrapIPARounds var)) (Vector slot1Width (Vector WrapIPARounds var))
      tup = genericFieldsToVar
        @(Tuple2 (Vector slot0Width (Vector WrapIPARounds a)) (Vector slot1Width (Vector WrapIPARounds a)))
        fs
    in
      uncurry2 (\slot0 slot1 -> WrapOldBpChals { slot0, slot1 }) tup

instance
  ( CheckedType f c (Vector slot0Width (Vector WrapIPARounds var))
  , CheckedType f c (Vector slot1Width (Vector WrapIPARounds var))
  ) =>
  CheckedType f c (WrapOldBpChals slot0Width slot1Width var) where
  check (WrapOldBpChals r) = check (tuple2 r.slot0 r.slot1)
