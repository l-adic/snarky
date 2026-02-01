module Snarky.Example.Types
  ( PublicKey(..)
  , TokenAmount(..)
  , Account(..)
  , Transaction
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class Hashable, class MerkleHashable)
import Data.Newtype (class Newtype, un)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class AssertEqual, class CheckedType, class CircuitM, class CircuitType, F(..), FVar, Snarky, assertEqGeneric, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.RandomOracle (Digest(..), hash2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Test.QuickCheck (class Arbitrary)

--------------------------------------------------------------------------------
-- | PublicKey type - a single field element representing a public key
newtype PublicKey f = PublicKey f

derive instance Newtype (PublicKey f) _
derive instance Generic (PublicKey f) _
derive newtype instance Show f => Show (PublicKey f)
derive newtype instance Eq f => Eq (PublicKey f)
derive newtype instance Ord f => Ord (PublicKey f)
derive newtype instance Arbitrary f => Arbitrary (PublicKey f)
derive instance Functor PublicKey

instance CircuitType f (PublicKey (F f)) (PublicKey (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(PublicKey (F f))
  fieldsToVar = genericFieldsToVar @(PublicKey (F f))

instance CheckedType f c t m (PublicKey (FVar f)) where
  check = genericCheck

instance CircuitM f c t m => AssertEqual f c t m (PublicKey (FVar f)) where
  assertEq x y = assertEqGeneric x y

--------------------------------------------------------------------------------
-- | TokenAmount type - a single field element representing a token balance
newtype TokenAmount f = TokenAmount f

derive instance Newtype (TokenAmount f) _
derive instance Generic (TokenAmount f) _
derive newtype instance Show f => Show (TokenAmount f)
derive newtype instance Eq f => Eq (TokenAmount f)
derive newtype instance Arbitrary f => Arbitrary (TokenAmount f)
derive instance Functor TokenAmount

derive newtype instance Semigroup f => Semigroup (TokenAmount f)
derive newtype instance Monoid f => Monoid (TokenAmount f)
derive newtype instance (Semiring f) => Semiring (TokenAmount f)
derive newtype instance (Ring f) => Ring (TokenAmount f)

instance CircuitType f (TokenAmount (F f)) (TokenAmount (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(TokenAmount (F f))
  fieldsToVar = genericFieldsToVar @(TokenAmount (F f))

instance CheckedType f c t m (TokenAmount (FVar f)) where
  check = genericCheck

--------------------------------------------------------------------------------
-- | Account type for merkle tree leaves
-- | Uses two field elements: publicKey and tokenBalance
newtype Account f = Account { publicKey :: PublicKey f, tokenBalance :: TokenAmount f }

derive instance Newtype (Account f) _
derive instance Generic (Account f) _
derive newtype instance Show f => Show (Account f)
derive instance Eq f => Eq (Account f)
derive newtype instance Arbitrary f => Arbitrary (Account f)
derive instance Functor Account

-- | CircuitType instance: Account (F f) <-> Account (FVar f)
instance CircuitType f (Account (F f)) (Account (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Account (F f))
  fieldsToVar = genericFieldsToVar @(Account (F f))

instance CheckedType f c t m (Account (FVar f)) where
  check = genericCheck

-- | Pure Hashable instance for Account (F f)
instance PoseidonField f => Hashable (Account (F f)) (Digest (F f)) where
  hash = case _ of
    Nothing -> Digest $ F $ Poseidon.hash []
    Just (Account { publicKey, tokenBalance }) ->
      let
        F pk = un PublicKey publicKey
        F tb = un TokenAmount tokenBalance
      in
        Digest $ F $ Poseidon.hash [ pk, tb ]

-- | Circuit Hashable instance for Account (FVar f)
instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  Hashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f))) where
  hash = case _ of
    Nothing -> hash2 (const_ zero) (const_ zero)
    Just (Account { publicKey, tokenBalance }) ->
      hash2 (un PublicKey publicKey) (un TokenAmount tokenBalance)

-- | MerkleHashable instance for pure Account
instance PoseidonField f => MerkleHashable (Account (F f)) (Digest (F f))

-- | MerkleHashable instance for circuit Account
instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))

--------------------------------------------------------------------------------
-- | Transaction type representing a transfer between accounts.
-- | Just specifies the public keys and amount - addresses are an internal detail
-- | that the prover looks up from the account map.
type Transaction f =
  { from :: PublicKey f
  , to :: PublicKey f
  , amount :: TokenAmount f
  }
