-- | Mina chain identifier — narrows the OCaml `Mina_signature_kind`
-- | ADT to the two cases this codebase supports (`Mainnet` and
-- | `Testnet`). `Other_network "<chain_name>"` is intentionally
-- | omitted; revisit if/when a custom network needs to be supported.
-- |
-- | The associated `signaturePrefix` gives the 3-element sponge
-- | prefix-state used by `Schnorr.Chunked` — `Hash_prefix_states.signature
-- | ~signature_kind` in mina. Each constant is byte-pasted from the
-- | output of
-- |   `dune exec src/lib/crypto/pickles/dump_schnorr_prefix_states/
-- |     dump_schnorr_prefix_states.exe`
-- | so it stays byte-identical to Mina's deployed prefix.
module Mina.ChainId
  ( ChainId(..)
  , chainIdFromTag
  , signaturePrefix
  , networkId
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Snarky.Curves.Class (fromHexLe)
import Snarky.Curves.Pallas as Pallas

data ChainId = Mainnet | Testnet

derive instance Eq ChainId
derive instance Ord ChainId
derive instance Generic ChainId _
instance Show ChainId where
  show = genericShow

-- | Parse a chain tag (the inverse of `show`); anything but `"Mainnet"` is testnet.
chainIdFromTag :: String -> ChainId
chainIdFromTag = case _ of
  "Mainnet" -> Mainnet
  _ -> Testnet

-- | `Hash_prefix_states.signature ~signature_kind` — the 3-element
-- | Poseidon-sponge state to seed a `Schnorr.Chunked` hash with for
-- | the given chain.
signaturePrefix :: ChainId -> Vector 3 Pallas.BaseField
signaturePrefix = case _ of
  Mainnet ->
    fromHexLe "494a6a0c1b0d8ca7bc1cef37a3d69c4133b8a994e760c2ff5ba1a723a67e393f"
      :< fromHexLe "4c2561efcd3dd41998ac7f4b20d12d2947bb0c4177d7f4e6a7753ccc78a4ce1c"
      :< fromHexLe "fbabea66d176d79be0265717a2ee07e019a7f9fe0638b128472fe9ed93e12305"
      :< Vector.nil
  Testnet ->
    fromHexLe "486a7ac50b48d60b4e844cdeac2aa487b85c68720d93bd64043bc1f839f7790e"
      :< fromHexLe "f1a03a60a27687f42330c6cf91acad27ad12b1739f229ba5c2b7f1debf171031"
      :< fromHexLe "1dfa8ba1eab55bbb8c3912f2f9c5a323fc8583af0979a499d5c4dc59b3a1f521"
      :< Vector.nil

-- | The 1-byte chain-id tag fed to `Data.Schnorr.Derive.derive`. Mirrors
-- | `Message.network_id_{mainnet,testnet}` in
-- | `mina/src/lib/crypto/signature_lib/schnorr.ml:308`.
networkId :: ChainId -> String
networkId = case _ of
  Mainnet -> "\x01"
  Testnet -> "\x00"
