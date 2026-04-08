-- | Pickles-specific type aliases for the Pasta 2-cycle.
-- |
-- | Centralizes field types, IPA round counts, commitment curve aliases,
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
  ) where

import Data.Tuple.Nested (Tuple2, Tuple3, tuple2, tuple3, uncurry2, uncurry3)
import Data.Vector (Vector)
import Pickles.Verify.Types (UnfinalizedProof, WrapDeferredValues)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToVar, genericFieldsToValue, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

-- | Step circuit field (Fp = Vesta.ScalarField = Pallas.BaseField).
type StepField = Vesta.ScalarField

-- | Wrap circuit field (Fq = Pallas.ScalarField = Vesta.BaseField).
type WrapField = Pallas.ScalarField

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = Rounds.Step = 16).
type StepIPARounds = 16

-- | IPA rounds in a Wrap proof (= log2 of Pallas SRS size = Rounds.Wrap = 15).
type WrapIPARounds = 15

-- | Maximum number of previous proofs verified per step (always 2 in Pickles).
-- | Reference: mina/src/lib/pickles/common/nat.ml (N2)
type MaxProofsVerified = 2

-- | Step proofs commit on Vesta (scalar field = Fp = StepField).
type StepCommitmentCurve = Vesta.G

-- | Wrap proofs commit on Pallas (scalar field = Fq = WrapField).
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
-- | The `fv` parameter is the field variable type (e.g., `FVar f` in circuits).
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
    let tup = genericFieldsToValue fs :: Tuple2 a a
    in uncurry2 (\zeta omegaTimesZeta -> PointEval { zeta, omegaTimesZeta }) tup
  varToFields (PointEval r) = genericVarToFields @(Tuple2 a a) (tuple2 r.zeta r.omegaTimesZeta)
  fieldsToVar fs =
    let tup = genericFieldsToVar @(Tuple2 a a) fs :: Tuple2 var var
    in uncurry2 (\zeta omegaTimesZeta -> PointEval { zeta, omegaTimesZeta }) tup

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
    let tup = genericFieldsToValue fs :: Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)
    in uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup
  varToFields (VerificationKey r) = genericVarToFields @(Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)) (tuple3 r.sigma r.coeff r.index)
  fieldsToVar fs =
    let tup = genericFieldsToVar @(Tuple3 (Vector 7 a) (Vector 15 a) (Vector 6 a)) fs :: Tuple3 (Vector 7 var) (Vector 15 var) (Vector 6 var)
    in uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup

instance (CheckedType f c var) => CheckedType f c (VerificationKey var) where
  check (VerificationKey r) = check (tuple3 r.sigma r.coeff r.index)
