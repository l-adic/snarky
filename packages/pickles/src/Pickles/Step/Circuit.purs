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
  -- * Step Circuit Types (re-exported from Pickles.Types)
  , module Pickles.Types
  -- * Step Circuit Combinator
  , stepCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.IPA (IpaScalarOps)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.Advice (class StepWitnessM, getProofWitnesses)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Types (StepInput, StepStatement)
import Pickles.Verify.Types (BulletproofChallenges, UnfinalizedProof)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assertEq, assert_, const_, exists, not_, or_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (Type2)

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
-- | Finalize Other Proof
-------------------------------------------------------------------------------

-- | Finalize another proof's deferred values.
-- |
-- | Wraps `finalizeOtherProofCircuit` with sponge initialization.
-- | Each proof gets its own fresh sponge state.
finalizeOtherProof
  :: forall _d d f f' g t m sf r r2
   . Add 1 _d d
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Reflectable d Int
  => { unshift :: sf -> FVar f
     , shiftedEqual :: sf -> FVar f -> Snarky (KimchiConstraint f) t m (BoolVar f)
     | r
     }
  -> FinalizeOtherProofParams f r2
  -> FVar f
  -> UnfinalizedProof d (FVar f) sf (BoolVar f)
  -> ProofWitness (FVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
finalizeOtherProof ops params prevChallengeDigest unfinalized witness =
  evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit ops params
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
  :: forall n d f c t m
   . PrimeField f
  => CircuitM f c t m
  => Vector n (BulletproofChallenges d (FVar f))
  -> Snarky c t m (FVar f)
hashMessagesForNextStepProofStub _challenges = do
  -- Stub: return zero digest
  pure $ const_ zero

-- | Stub: Compute message digest for next Wrap proof.
-- |
-- | Reference: step_main.ml:478-482
computeMessageForNextWrapProofStub
  :: forall d f c t m
   . PrimeField f
  => CircuitM f c t m
  => BulletproofChallenges d (FVar f)
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
-- | assertion passes trivially. Pass dummy `previousProofInputs` and `unfinalizedProofs`.
-- | Proof witnesses are provided privately via `StepWitnessM`.
stepCircuit
  :: forall n ds _dw dw input prevInput output aux t m r
   . Add 1 _dw dw
  => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => StepWitnessM n dw m Vesta.ScalarField
  => Reflectable n Int
  => Reflectable dw Int
  => IpaScalarOps Vesta.ScalarField t m (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))
  -> FinalizeOtherProofParams Vesta.ScalarField r
  -> AppCircuit n input prevInput output aux Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  -> StepInput n input prevInput ds dw (FVar Vesta.ScalarField) (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField)) (BoolVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t m (StepStatement n ds dw (FVar Vesta.ScalarField) (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField)) (BoolVar Vesta.ScalarField))
stepCircuit ops params appCircuit { appInput, previousProofInputs, unfinalizedProofs, prevChallengeDigests } = do
  -- 1. Run application circuit
  { mustVerify } <- appCircuit { appInput, previousProofInputs }

  -- 2. Request private proof witnesses via advisory monad
  proofWitnesses <- exists $ lift $ getProofWitnesses @_ @dw unit

  -- 3. For each previous proof, verify and collect challenges
  let
    proofsWithData = Vector.zip (Vector.zip (Vector.zip unfinalizedProofs proofWitnesses) prevChallengeDigests) mustVerify

  challengesAndDigests <- for proofsWithData \(Tuple (Tuple (Tuple unfinalized witness) prevChallengeDigest) mustVerifyFlag) -> do
    let
      shouldFinalize = unfinalized.shouldFinalize

    -- 3a. Assert shouldFinalize == mustVerify (step_main.ml:34)
    assertEq shouldFinalize mustVerifyFlag

    -- 3b. Finalize the proof
    { finalized, challenges } <- finalizeOtherProof ops params prevChallengeDigest unfinalized witness

    -- 3c. Key assertion: finalized || not shouldFinalize (wrap_main.ml:431)
    -- This is how bootstrapping works: dummies have shouldFinalize = false,
    -- so `not shouldFinalize = true`, and the assertion passes.
    finalizedOrNotRequired <- or_ finalized (not_ shouldFinalize)
    assert_ finalizedOrNotRequired

    -- 3d. Compute message for next Wrap proof
    messageForWrap <- computeMessageForNextWrapProofStub challenges

    pure { challenges, messageForWrap }

  -- 4. Extract challenges and messages
  let
    allChallenges = map _.challenges challengesAndDigests
    messagesForNextWrapProof = map _.messageForWrap challengesAndDigests

  -- 5. Hash messages for next Step proof
  messagesForNextStepProof <- hashMessagesForNextStepProofStub allChallenges

  -- 6. Return StepStatement
  pure
    { proofState:
        { unfinalizedProofs
        , messagesForNextStepProof
        }
    , messagesForNextWrapProof
    }
