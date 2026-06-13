-- | Random transaction *scenarios* for the simulation: pick a sender/receiver
-- | pair from the ledger and produce either a valid transfer (amount below the
-- | sender's balance) or an overdraft (amount above it, which the circuit must
-- | reject). The ledger lives in `Snarky.Example.Ledger`, `sign` in
-- | `Snarky.Example.Transaction`, and the signing keys come from the
-- | simulation `Keystore`.
module Snarky.Example.Simulation.Transaction
  ( genDistinctPublicKeys
  , genValidSignedTransaction
  , genOverdraftSignedTransaction
  ) where

import Prelude

import Control.Monad.Gen (chooseInt) as MonadGen
import Data.Array (length, (!!), (..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Set as Set
import Data.Traversable (for)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Mina.ChainId (ChainId)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (fromBigInt, toBigInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Simulation.Keystore (Keystore, senderInfo)
import Snarky.Example.Transaction (SignedTransaction, sign)
import Snarky.Example.Types (PublicKey, mkAmount)
import Test.QuickCheck.Gen (Gen, chooseInt, suchThat)

-- | Pick two distinct public keys from the ledger's account index.
genDistinctPublicKeys
  :: forall d
   . Ledger d
  -> Gen { fromPk :: PublicKey Vesta.ScalarField, toPk :: PublicKey Vesta.ScalarField }
genDistinctPublicKeys ledger = do
  let
    keys :: Array (PublicKey Vesta.ScalarField)
    keys = Set.toUnfoldable $ Map.keys ledger.accountMap
    maxIdx = length keys - 1
  fromIdx <- chooseInt 0 maxIdx
  toIdx <- chooseInt 0 maxIdx `suchThat` (\i -> i /= fromIdx)
  pure
    { fromPk: unsafePartial fromJust $ keys !! fromIdx
    , toPk: unsafePartial fromJust $ keys !! toIdx
    }

-- | Generate a valid, signed transfer against the given ledger + wallet,
-- | signed under `chainId` (must match the verifier's chain id).
genValidSignedTransaction
  :: forall d
   . ChainId
  -> Ledger d
  -> Keystore
  -> Gen (SignedTransaction Vesta.ScalarField)
genValidSignedTransaction chainId ledger wallet = do
  { fromPk, toPk } <- genDistinctPublicKeys ledger
  let { privateKey, nonce, balance } = senderInfo ledger wallet fromPk
  -- Pick a valid transfer amount (less than the sender's balance).
  amountInt <- chooseBigInt one (max one (toBigInt balance - one))
  let amount = unsafePartial fromJust $ mkAmount (fromBigInt amountInt)
  pure $ sign privateKey chainId nonce { amount, to: toPk }

-- | Generate a correctly-signed transfer whose amount exceeds the
-- | sender's balance (so the in-circuit underflow check must reject it).
genOverdraftSignedTransaction
  :: forall d
   . ChainId
  -> Ledger d
  -> Keystore
  -> Gen (SignedTransaction Vesta.ScalarField)
genOverdraftSignedTransaction chainId ledger wallet = do
  { fromPk, toPk } <- genDistinctPublicKeys ledger
  let
    { privateKey, nonce, balance } = senderInfo ledger wallet fromPk
    amount = unsafePartial fromJust $ mkAmount (balance + one)
  pure $ sign privateKey chainId nonce { amount, to: toPk }

--------------------------------------------------------------------------------

-- | Generate a random BigInt in the range [a, b] (inclusive).
chooseBigInt :: BigInt -> BigInt -> Gen BigInt
chooseBigInt a b
  | a > b = chooseBigInt b a
  | otherwise = (\x -> x + a) <$> chooseBigInt' (b - a)

-- | Generate a random BigInt in the range [0, range] (inclusive).
chooseBigInt' :: BigInt -> Gen BigInt
chooseBigInt' range =
  case BigInt.toInt range of
    -- Common case: range fits in Int32
    Just n -> BigInt.fromInt <$> MonadGen.chooseInt 0 n
    -- Large range: generate random bits and mod
    Nothing -> do
      let
        numBits = bitLength range
        stepChunks = (numBits + 30) / 31 -- 31 bits per chunk (safe Int)
      -- Generate random 31-bit chunks
      chunks <- for (1 .. stepChunks) \_ -> BigInt.fromInt <$> MonadGen.chooseInt 0 0x7FFFFFFF
      -- Combine chunks into a single BigInt
      let randomBits = foldlChunks chunks
      -- Mod by (range + 1) to get value in [0, range]
      pure $ randomBits `mod` (range + BigInt.fromInt 1)
  where
  -- Combine chunks: each chunk contributes 31 bits
  foldlChunks :: Array BigInt -> BigInt
  foldlChunks =
    let
      base = BigInt.fromInt 0x40000000 * BigInt.fromInt 2 -- 2^31
    in
      foldl (\acc chunk -> acc * base + chunk) (BigInt.fromInt 0)

  -- Count bits needed to represent n
  bitLength :: BigInt -> Int
  bitLength n
    | n <= BigInt.fromInt 0 = 0
    | otherwise = 1 + bitLength (n / BigInt.fromInt 2)
