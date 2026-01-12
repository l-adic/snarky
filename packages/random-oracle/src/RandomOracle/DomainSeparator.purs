-- | Domain separation for random oracles (mina-hasher compatible).
-- |
-- | This module provides domain separation functionality that matches
-- | the mina-hasher Rust implementation exactly.
module RandomOracle.DomainSeparator
  ( class HasDomainSeparator
  , initWithDomain
  ) where

import Data.Vector (Vector)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Type class for fields that support mina-hasher compatible domain separation.
-- |
-- | Domain separation works by:
-- | 1. Converting a domain string to a field element (truncated to 20 chars,
-- |    right-padded with '*', zero-padded to 32 bytes, little-endian from_bytes)
-- | 2. Absorbing that field element into a fresh sponge
-- | 3. Squeezing to get the initial state for subsequent hashing
class HasDomainSeparator f where
  -- | Initialize sponge state with domain separation.
  -- | Returns the 3-element state after absorbing domain and squeezing.
  initWithDomain :: String -> Vector 3 f

foreign import pallasInitWithDomain :: String -> Vector 3 Pallas.BaseField
foreign import vestaInitWithDomain :: String -> Vector 3 Vesta.BaseField

instance HasDomainSeparator Pallas.BaseField where
  initWithDomain = pallasInitWithDomain

instance HasDomainSeparator Vesta.BaseField where
  initWithDomain = vestaInitWithDomain
