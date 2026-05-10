-- | Public API for Pickles side-loaded verification keys: the
-- | wrap-proof verification key supplied at runtime rather than baked
-- | into compile output, used inside a step circuit to verify a
-- | side-loaded child's wrap proof.
-- |
-- | The `VerificationKey` type is opaque — construct via
-- | `fromCompiledWrap` (for PS-side compiled children). Library code
-- | that needs the data constructor or the compile-time placeholder
-- | imports `Pickles.Sideload.VerificationKey.Internal`.
-- |
-- | Reference: OCaml `Pickles.Side_loaded.Verification_key`.
module Pickles.Sideload.VerificationKey
  ( module Reexport
  ) where

import Pickles.Sideload.VerificationKey.Internal
  ( Checked(..)
  , ProofsVerified(..)
  , ProofsVerifiedCount
  , VerificationKey
  , VerificationKeyVar
  , boolVecToProofsVerified
  , fromCompiledWrap
  ) as Reexport
