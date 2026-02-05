-- | Step circuit combinator for Pickles recursion.
-- |
-- | The Step circuit combines an application circuit with verification of
-- | previous Wrap proofs. It handles both base case (no real proofs) and
-- | recursive cases (verifying previous Wrap proofs).
-- |
-- | Key mechanism: The `shouldFinalize` flag enables bootstrapping. Dummy proofs
-- | have `shouldFinalize = false`, which makes `finalized || not shouldFinalize`
-- | pass regardless of verification result.
-- |
-- | Reference: mina/src/lib/pickles/step_main.ml:274-594
module Pickles.Step.Circuit
  ( -- * Application Circuit Types
    PreviousProofStatement
  , StepReturn
  -- * Step Circuit Types
  , StepStatement
  -- * Step Circuit Combinator
  , stepCircuit
  ) where

import Prelude

import Data.Newtype (unwrap)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Step.Types (BulletproofChallenges(..), ScalarChallenge, UnfinalizedProof)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, assertEq, assert_, const_, not_, or_)
import Snarky.Circuit.DSL.Monad (Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.SizedF (SizedF(..))
import Snarky.Types.Shifted (Type1)

-------------------------------------------------------------------------------
-- | Application Circuit Types
-------------------------------------------------------------------------------

-- | A previous proof statement from the application circuit.
-- |
-- | The `mustVerify` flag indicates whether this proof should actually be verified.
-- | For base case (Step0), all `mustVerify` flags are false.
-- |
-- | Reference: pickles_intf.mli:168-178 `Previous_proof_statement`
type PreviousProofStatement publicInput f =
  { publicInput :: publicInput
  , mustVerify :: BoolVar f
  -- Note: proof witness is passed separately to stepCircuit
  }

-- | Return type from an application circuit.
-- |
-- | The application circuit returns previous proof statements (with mustVerify flags)
-- | and its public output. The auxiliary output is private prover data.
-- |
-- | Reference: pickles_intf.mli:184-190 `main_return`
type StepReturn n publicInput publicOutput aux f =
  { previousProofStatements :: Vector n (PreviousProofStatement publicInput f)
  , publicOutput :: publicOutput
  , auxiliaryOutput :: aux
  }

-------------------------------------------------------------------------------
-- | Step Circuit Output Types
-------------------------------------------------------------------------------

-- | The Step circuit's output statement.
-- |
-- | This becomes part of the public input for the Wrap circuit to verify.
-- |
-- | The `fv` parameter is the field variable type (e.g., `FVar f` in circuits).
-- | The `sf` parameter is the shifted value type (e.g., `Type1 (FVar f)`).
-- | The `b` parameter is the boolean type (e.g., `BoolVar f`).
-- |
-- | Reference: step_main.ml:587-594 `Types.Step.Statement`
type StepStatement n fv sf b =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof fv sf b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-------------------------------------------------------------------------------
-- | Circuit-Compatible Dummy Values
-------------------------------------------------------------------------------

-- | Dummy scalar challenge as a circuit constant.
dummyScalarChallengeVar :: forall f. PrimeField f => ScalarChallenge (FVar f)
dummyScalarChallengeVar = SizedF (const_ zero)

-- | Dummy bulletproof challenges as circuit constants.
-- |
-- | These are all-zero challenges lifted into the circuit with `const_`.
dummyBulletproofChallengesVar :: forall f. PrimeField f => BulletproofChallenges (FVar f)
dummyBulletproofChallengesVar = BulletproofChallenges $ Vector.generate \_ -> dummyScalarChallengeVar

-------------------------------------------------------------------------------
-- | Step Circuit Combinator
-------------------------------------------------------------------------------

-- | Type alias for an application circuit in the Step context.
-- |
-- | Takes the application's public input and returns:
-- | - Previous proof statements with mustVerify flags
-- | - Public output
-- | - Auxiliary (private) output
type AppCircuit n input prevInput output aux f c t m =
  input
  -> Snarky c t m (StepReturn n prevInput output aux f)

-- | Stub: Finalize another proof's deferred values.
-- |
-- | In the full implementation, this checks:
-- | - xi_correct (scalar challenge matches squeezed value)
-- | - b_correct (challenge polynomial evaluation)
-- | - combined_inner_product_correct
-- | - plonk_checks_passed (gate constraints, permutation)
-- |
-- | For now, returns (true, dummy challenges) to enable skeleton testing.
-- |
-- | Reference: step_verifier.ml:823-1086 `finalize_other_proof`
finalizeOtherProofStub
  :: forall f c t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f c t m
  => UnfinalizedProof (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> Snarky c t m { finalized :: BoolVar f, challenges :: BulletproofChallenges (FVar f) }
finalizeOtherProofStub _unfinalized = do
  -- Stub: always return true and dummy challenges
  pure
    { finalized: const_ one
    , challenges: dummyBulletproofChallengesVar
    }

-- | Stub: Hash messages for the next Step proof.
-- |
-- | Hashes the application state and bulletproof challenges into a single digest.
-- | The exact hashing scheme follows Pickles conventions.
-- |
-- | Reference: step_verifier.ml:1099+
hashMessagesForNextStepProofStub
  :: forall n f c t m
   . PrimeField f
  => CircuitM f c t m
  => Vector n (BulletproofChallenges (FVar f))
  -> Snarky c t m (FVar f)
hashMessagesForNextStepProofStub _challenges = do
  -- Stub: return zero digest
  pure $ const_ zero

-- | Stub: Compute message digest for next Wrap proof.
-- |
-- | Reference: step_main.ml:478-482
computeMessageForNextWrapProofStub
  :: forall f c t m
   . PrimeField f
  => CircuitM f c t m
  => BulletproofChallenges (FVar f)
  -> Snarky c t m (FVar f)
computeMessageForNextWrapProofStub _challenges = do
  -- Stub: return zero digest
  pure $ const_ zero

-- | The Step circuit combinator.
-- |
-- | Combines an application circuit with verification of previous Wrap proofs.
-- |
-- | **Processing (see step_main.ml:274-594):**
-- | 1. Run application circuit → get `previousProofStatements` with `mustVerify` flags
-- | 2. For each previous proof:
-- |    - Assert `unfinalizedProof.shouldFinalize == statement.mustVerify`
-- |    - Call `finalizeOtherProof` → `(finalized, challenges)`
-- |    - Assert `finalized || not shouldFinalize` (key bootstrapping assertion)
-- | 3. Collect bulletproof challenges
-- | 4. Hash messages for next Step proof
-- | 5. Return StepStatement
-- |
-- | **For base case (Step0):** All `shouldFinalize = false`, all `mustVerify = false`,
-- | assertion passes trivially.
-- |
-- | Note: This is a skeleton implementation. `finalizeOtherProof` and hashing
-- | are stubbed out - they return dummy values to enable testing the circuit structure.
stepCircuit
  :: forall n input prevInput output aux f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => AppCircuit n input prevInput output aux f (KimchiConstraint f) t m
  -> { appInput :: input
     , unfinalizedProofs :: Vector n (UnfinalizedProof (FVar f) (Type1 (FVar f)) (BoolVar f))
     }
  -> Snarky (KimchiConstraint f) t m (StepStatement n (FVar f) (Type1 (FVar f)) (BoolVar f))
stepCircuit appCircuit { appInput, unfinalizedProofs } = do
  -- 1. Run application circuit
  { previousProofStatements } <- appCircuit appInput

  -- 2. For each previous proof, verify and collect challenges
  let
    stmtsAndProofs = Vector.zip previousProofStatements unfinalizedProofs

  challengesAndDigests <- for stmtsAndProofs \(Tuple stmt unfinalized) -> do
    let
      { mustVerify } = stmt
      shouldFinalize = (unwrap unfinalized).shouldFinalize

    -- 2a. Assert shouldFinalize == mustVerify (step_main.ml:34)
    -- Note: For proper implementation, this should use assertEqual_ on BoolVars
    -- For skeleton, we just check they're consistent
    assertEq shouldFinalize mustVerify

    -- 2b. Finalize the proof (stub for now)
    { finalized, challenges } <- finalizeOtherProofStub unfinalized

    -- 2c. Key assertion: finalized || not shouldFinalize (wrap_main.ml:431)
    -- This is how bootstrapping works: dummies have shouldFinalize = false,
    -- so `not shouldFinalize = true`, and the assertion passes.
    finalizedOrNotRequired <- or_ finalized (not_ shouldFinalize)
    assert_ finalizedOrNotRequired

    -- 2d. Compute message for next Wrap proof
    messageForWrap <- computeMessageForNextWrapProofStub challenges

    pure { challenges, messageForWrap }

  -- 3. Extract challenges and messages
  let
    allChallenges = map _.challenges challengesAndDigests
    messagesForNextWrapProof = map _.messageForWrap challengesAndDigests

  -- 4. Hash messages for next Step proof
  messagesForNextStepProof <- hashMessagesForNextStepProofStub allChallenges

  -- 5. Return StepStatement
  pure
    { proofState:
        { unfinalizedProofs
        , messagesForNextStepProof
        }
    , messagesForNextWrapProof
    }