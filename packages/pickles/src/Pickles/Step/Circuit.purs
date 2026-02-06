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
    AppCircuit
  , AppCircuitInput
  , AppCircuitOutput
  -- * Step Circuit Types
  , StepInput
  , StepStatement
  -- * Step Circuit Combinator
  , stepCircuit
  ) where

import Prelude

import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Step.Types (BulletproofChallenges, UnfinalizedProof)
import Pickles.Step.WrapProofWitness (WrapProofWitness)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assertEq, assert_, const_, not_, or_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)
import Snarky.Types.Shifted (Type1)

-------------------------------------------------------------------------------
-- | Application Circuit Types
-------------------------------------------------------------------------------

-- | Input to an application circuit.
-- |
-- | The application receives:
-- | - `appInput`: Its own application-specific input
-- | - `previousProofInputs`: Public inputs from previous proofs (for recursive apps)
-- |
-- | For base case (no recursion), `previousProofInputs` contains dummy values.
type AppCircuitInput n input prevInput =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  }

-- | Output from an application circuit.
-- |
-- | The application returns:
-- | - `mustVerify`: Which previous proofs should actually be verified
-- | - `publicOutput`: The application's public output
-- | - `auxiliaryOutput`: Private prover data (not part of public statement)
-- |
-- | For base case, `mustVerify` should be all false.
type AppCircuitOutput n output aux f =
  { mustVerify :: Vector n (BoolVar f)
  , publicOutput :: output
  , auxiliaryOutput :: aux
  }

-- | Type alias for an application circuit in the Step context.
-- |
-- | An application circuit:
-- | 1. Receives its input + previous proof public inputs
-- | 2. Does its application logic (e.g., verify a signature)
-- | 3. Returns which previous proofs to verify + its output
-- |
-- | The Step combinator handles the actual verification of previous proofs.
type AppCircuit n input prevInput output aux f c t m =
  AppCircuitInput n input prevInput
  -> Snarky c t m (AppCircuitOutput n output aux f)

-------------------------------------------------------------------------------
-- | Step Circuit Types
-------------------------------------------------------------------------------

-- | Input to the Step circuit combinator.
-- |
-- | Bundles the application input with the proof witness data.
-- |
-- | Parameters:
-- | - `n`: Number of previous proofs to verify
-- | - `input`: Application-specific input type
-- | - `prevInput`: Previous proof public input type
-- | - `f`: Field element type
-- | - `sf`: Shifted scalar type
-- | - `b`: Boolean type
type StepInput n input prevInput f sf b =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  , unfinalizedProofs :: Vector n (UnfinalizedProof f sf b)
  , wrapProofWitnesses :: Vector n (WrapProofWitness f)
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
type StepStatement n fv sf b =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof fv sf b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-------------------------------------------------------------------------------
-- | Finalize Other Proof
-------------------------------------------------------------------------------

-- | Finalize another proof's deferred values.
-- |
-- | Wraps `finalizeOtherProofCircuit` with sponge initialization.
-- | Each proof gets its own fresh sponge state.
finalizeOtherProof
  :: forall f f' t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => FinalizeOtherProofParams f
  -> FVar f
  -> UnfinalizedProof (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> WrapProofWitness (FVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput f)
finalizeOtherProof params prevChallengeDigest unfinalized witness =
  evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit params
      { unfinalized, witness, prevChallengeDigest }

-------------------------------------------------------------------------------
-- | Stub Implementations (to be replaced)
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- | Step Circuit Combinator
-------------------------------------------------------------------------------

-- | The Step circuit combinator.
-- |
-- | Takes an application circuit and returns a Step circuit that:
-- | 1. Runs the application circuit
-- | 2. Verifies previous Wrap proofs based on `mustVerify` flags
-- | 3. Returns a StepStatement for the Wrap circuit
-- |
-- | **Processing (see step_main.ml:274-594):**
-- | 1. Run application circuit -> get `mustVerify` flags
-- | 2. For each previous proof where `mustVerify = true`:
-- |    - Assert `unfinalizedProof.shouldFinalize == mustVerify`
-- |    - Call `finalizeOtherProof` -> `(finalized, challenges)`
-- |    - Assert `finalized || not shouldFinalize` (key bootstrapping assertion)
-- | 3. Collect bulletproof challenges
-- | 4. Hash messages for next Step proof
-- | 5. Return StepStatement
-- |
-- | **For base case (Step0):** All `shouldFinalize = false`, all `mustVerify = false`,
-- | assertion passes trivially. Pass dummy `previousProofInputs`, `unfinalizedProofs`,
-- | and `wrapProofWitnesses`.
stepCircuit
  :: forall n input prevInput output aux f f' t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => FinalizeOtherProofParams f
  -> AppCircuit n input prevInput output aux f (KimchiConstraint f) t m
  -> StepInput n input prevInput (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (StepStatement n (FVar f) (Type1 (FVar f)) (BoolVar f))
stepCircuit params appCircuit { appInput, previousProofInputs, unfinalizedProofs, wrapProofWitnesses, prevChallengeDigests } = do
  -- 1. Run application circuit
  { mustVerify } <- appCircuit { appInput, previousProofInputs }

  -- 2. For each previous proof, verify and collect challenges
  let
    proofsWithData = Vector.zip (Vector.zip (Vector.zip unfinalizedProofs wrapProofWitnesses) prevChallengeDigests) mustVerify

  challengesAndDigests <- for proofsWithData \(Tuple (Tuple (Tuple unfinalized witness) prevChallengeDigest) mustVerifyFlag) -> do
    let
      shouldFinalize = unfinalized.shouldFinalize

    -- 2a. Assert shouldFinalize == mustVerify (step_main.ml:34)
    assertEq shouldFinalize mustVerifyFlag

    -- 2b. Finalize the proof
    { finalized, challenges } <- finalizeOtherProof params prevChallengeDigest unfinalized witness

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
