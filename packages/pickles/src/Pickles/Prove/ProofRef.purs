-- | A claimed statement and its eventual proof. Reference construction
-- | does not execute the rule; local fulfillment calls its full prover.
module Pickles.Prove.ProofRef
  ( ProofRef
  , proofRef
  , proofStatement
  , initialStatement
  , importProof
  , ProofProvider
  , localProofProvider
  ) where

import Prelude

import Data.Either (Either, either)
import Effect (Effect)
import Effect.Exception (Error)
import Effect.Exception as Exc
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles.Field (StepField)
import Pickles.Prove.Types (BranchProver(..))
import Pickles.Types (ApplicationStatement(..))
import Pickles.Verify (CompiledProof(..))
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.EvalError (throwEvalError)
import Snarky.Circuit.Types (class CircuitType, valueToFields)

-- | Opaque to application rules. A reference can be shared by several
-- | parents; fulfilling it does not consume its completed proof.
newtype ProofRef :: Int -> Type -> Type
newtype ProofRef n stmt = ProofRef
  { statement :: stmt
  , fulfill :: Effect (CompiledProof n stmt)
  }

data LocalProofState :: Int -> Type -> Type
data LocalProofState n stmt
  = Pending (Effect (CompiledProof n stmt))
  | Resolved (Either Error (CompiledProof n stmt))

-- | Register a local invocation for a claimed statement. The input is
-- | taken from that statement; the output is checked when proof debt
-- | requires fulfillment. The caller supplies a compiled branch and
-- | its ordinary advice and slots.
proofRef
  :: forall prevsSpec n prevsCarrier inputVal inputVar outputVal outputVar r
   . CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => BranchProver prevsSpec n prevsCarrier inputVal outputVal r
  -> AdviceHandler r
  -> { statement :: ApplicationStatement inputVal outputVal
     , prevs :: prevsCarrier
     }
  -> Effect (ProofRef n (ApplicationStatement inputVal outputVal))
proofRef (BranchProver { prove }) handler { statement, prevs } = do
  state <- Ref.new $ Pending do
    let ApplicationStatement claimed = statement
    proof@(CompiledProof completed) <-
      prove handler { appInput: claimed.input, prevs } >>= either throwEvalError pure
    unless (valueToFields @StepField completed.statement == valueToFields @StepField statement) $
      throwEvalError (FailedAssertion "proof reference: completed proof does not match the claimed statement")
    pure proof
  pure $ ProofRef { statement, fulfill: fulfillCached state }

-- | Read the claim without requesting any proving work.
proofStatement :: forall n stmt. ProofRef n stmt -> stmt
proofStatement (ProofRef ref) = ref.statement

-- | A chain's initial statement has no producing invocation. A rule
-- | may read it, but attempting to require its proof is an error.
initialStatement :: forall n stmt. stmt -> ProofRef n stmt
initialStatement statement = ProofRef
  { statement
  , fulfill: throwEvalError (FailedAssertion "proof reference: required proof has no producing invocation")
  }

-- | A completed proof, for example one received from another process.
-- | The consuming circuit still verifies it against its declared slot.
importProof :: forall n stmt. CompiledProof n stmt -> ProofRef n stmt
importProof proof@(CompiledProof completed) =
  ProofRef { statement: completed.statement, fulfill: pure proof }

-- | Runtime operations, separate from the rule's statement/debt API.
-- | The first implementation is synchronous and runs in `Effect`.
type ProofProvider =
  { fulfill :: forall n stmt. ProofRef n stmt -> Effect (CompiledProof n stmt)
  }

localProofProvider :: ProofProvider
localProofProvider = { fulfill: \(ProofRef ref) -> ref.fulfill }

-- | Only pending local invocations allocate a cache. The fulfillment
-- | action captures this cell, so sharing a reference shares its result.
fulfillCached
  :: forall n stmt
   . Ref (LocalProofState n stmt)
  -> Effect (CompiledProof n stmt)
fulfillCached state = Ref.read state >>= case _ of
  Pending prove -> do
    completed <- Exc.try prove
    -- Replacing the pending action releases the retained invocation,
    -- including its advice and child references, on success or failure.
    Ref.write (Resolved completed) state
    either Exc.throwException pure completed
  Resolved completed -> either Exc.throwException pure completed
