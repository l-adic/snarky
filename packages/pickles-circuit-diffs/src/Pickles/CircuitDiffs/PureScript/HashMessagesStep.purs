module Pickles.CircuitDiffs.PureScript.HashMessagesStep
  ( compileHashMessagesStep
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.Tuple.Nested (Tuple2, Tuple3, tuple2, tuple3, uncurry2, uncurry3)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Types (WrapIPARounds)
import Pickles.VerificationKey (VerificationKey)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, Snarky, UnChecked(..), assertEq, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, varToFields)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | One previous proof's messages: its `sg` and its 15 expanded challenges.
newtype PrevProofMessages f pt = PrevProofMessages
  { challengePolynomialCommitment :: pt
  , oldBulletproofChallenges :: Vector WrapIPARounds f
  }

-- | The wire order.
type PrevProofMessagesTuple f pt = Tuple2 pt (Vector WrapIPARounds f)

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  ) =>
  CircuitType f (PrevProofMessages fa pa) (PrevProofMessages fv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PrevProofMessagesTuple fa pa))
  valueToFields = genericValueToFields <<< prevToTuple
  fieldsToValue = prevFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(PrevProofMessagesTuple fa pa) <<< prevToTuple
  fieldsToVar = prevFromTuple <<< genericFieldsToVar @(PrevProofMessagesTuple fa pa)

prevToTuple :: forall f pt. PrevProofMessages f pt -> PrevProofMessagesTuple f pt
prevToTuple (PrevProofMessages p) = tuple2 p.challengePolynomialCommitment p.oldBulletproofChallenges

prevFromTuple :: forall f pt. PrevProofMessagesTuple f pt -> PrevProofMessages f pt
prevFromTuple = uncurry2 \challengePolynomialCommitment oldBulletproofChallenges ->
  PrevProofMessages { challengePolynomialCommitment, oldBulletproofChallenges }

-- | `hash_messages_for_next_step_proof_circuit`'s input (OCaml `dump_circuit_impl.ml`): the
-- | wrap key's commitments, the two previous proofs' messages, and the claimed digest.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_verifier.ml
-- |   sponge_after_index (lines 1167-1176)
-- |   hash_messages_for_next_step_proof (lines 1178-1188)
newtype HashMessagesStepInput f pt = HashMessagesStepInput
  { vk :: VerificationKey 1 pt
  , proofs :: Vector 2 (PrevProofMessages f pt)
  , claimedDigest :: f
  }

-- | The wire order.
type HashMessagesStepTuple f pt = Tuple3 (VerificationKey 1 pt) (Vector 2 (PrevProofMessages f pt)) f

toTuple :: forall f pt. HashMessagesStepInput f pt -> HashMessagesStepTuple f pt
toTuple (HashMessagesStepInput i) = tuple3 i.vk i.proofs i.claimedDigest

fromTuple :: forall f pt. HashMessagesStepTuple f pt -> HashMessagesStepInput f pt
fromTuple = uncurry3 \vk proofs claimedDigest -> HashMessagesStepInput { vk, proofs, claimedDigest }

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  ) =>
  CircuitType f (HashMessagesStepInput fa pa) (HashMessagesStepInput fv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(HashMessagesStepTuple fa pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(HashMessagesStepTuple fa pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(HashMessagesStepTuple fa pa)

hashMessagesStepCircuit
  :: forall r
   . UnChecked (HashMessagesStepInput (FVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
hashMessagesStepCircuit (UnChecked (HashMessagesStepInput i)) = do
  -- 1. sponge_after_index: absorb the key's commitments, sigma, coefficients, index
  spongeAfterIndex <-
    foldM (\s x -> Sponge.absorb x s) initialSpongeCircuit
      (varToFields @StepField @(VerificationKey 1 (AffinePoint StepField)) i.vk)

  -- 2. Absorb to_field_elements_without_index (app_state = unit, so just sg + bp_challenges)
  let
    absorbProof s (PrevProofMessages p) = do
      let AffinePoint sg = p.challengePolynomialCommitment
      s1 <- Sponge.absorb sg.x s
      s2 <- Sponge.absorb sg.y s1
      foldM (\s' x -> Sponge.absorb x s') s2 p.oldBulletproofChallenges
  sponge <- foldM absorbProof spongeAfterIndex i.proofs

  -- 3. Squeeze the digest and assert it matches the claim
  { result: digest } <- Sponge.squeeze sponge
  assertEq digest i.claimedDigest

compileHashMessagesStep :: Effect (CompiledCircuit StepField)
compileHashMessagesStep =
  compile noAdvice (Proxy @(UnChecked (HashMessagesStepInput (F StepField) (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    hashMessagesStepCircuit
