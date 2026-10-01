module Pickles.CircuitDiffs.PureScript.HashMessagesWrap
  ( compileHashMessagesWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (MessagesForNextWrapProof(..), WrapIPARounds)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofCircuit')
import RandomOracle.Sponge (Sponge) as RO
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, Snarky, UnChecked(..), assertEq, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | `hash_messages_for_next_wrap_proof_circuit`'s input (OCaml `dump_circuit_impl.ml`), at
-- | `MaxProofsVerified = 2`: the challenges first, in the hash's absorb order.
-- |
-- | Reference: mina/src/lib/pickles/wrap_hack.ml:119-142
newtype HashMessagesWrapInput f pt = HashMessagesWrapInput
  { oldBulletproofChallenges :: Vector 2 (Vector WrapIPARounds f)
  , challengePolynomialCommitment :: pt
  , claimedDigest :: f
  }

-- | The wire order.
type HashMessagesWrapTuple f pt = Tuple3 (Vector 2 (Vector WrapIPARounds f)) pt f

toTuple :: forall f pt. HashMessagesWrapInput f pt -> HashMessagesWrapTuple f pt
toTuple (HashMessagesWrapInput i) =
  tuple3 i.oldBulletproofChallenges i.challengePolynomialCommitment i.claimedDigest

fromTuple :: forall f pt. HashMessagesWrapTuple f pt -> HashMessagesWrapInput f pt
fromTuple = uncurry3 \oldBulletproofChallenges challengePolynomialCommitment claimedDigest ->
  HashMessagesWrapInput { oldBulletproofChallenges, challengePolynomialCommitment, claimedDigest }

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  ) =>
  CircuitType f (HashMessagesWrapInput fa pa) (HashMessagesWrapInput fv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(HashMessagesWrapTuple fa pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(HashMessagesWrapTuple fa pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(HashMessagesWrapTuple fa pa)

hashMessagesWrapCircuit
  :: forall r
   . UnChecked (HashMessagesWrapInput (FVar WrapField) (AffinePoint (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
hashMessagesWrapCircuit (UnChecked (HashMessagesWrapInput i)) = do
  digest <- evalSpongeM (initialSpongeCircuit :: RO.Sponge (FVar WrapField)) $
    hashMessagesForNextWrapProofCircuit'
      ( MessagesForNextWrapProof
          { challengePolynomialCommitment: i.challengePolynomialCommitment
          , oldBulletproofChallenges: i.oldBulletproofChallenges
          }
      )
  assertEq digest i.claimedDigest

compileHashMessagesWrap :: Effect (CompiledCircuit WrapField)
compileHashMessagesWrap =
  compile noAdvice (Proxy @(UnChecked (HashMessagesWrapInput (F WrapField) (AffinePoint WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    hashMessagesWrapCircuit
