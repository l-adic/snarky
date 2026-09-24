-- | Public API for Pickles side-loading: runtime-supplied wrap
-- | verification keys + the kimchi FFI for loading them from JSON.
-- |
-- | A re-export facade. Everything not re-exported here — the
-- | in-circuit side-loading machinery — is not part of the public
-- | surface.
module Pickles.Sideload
  ( module Pickles.Sideload.Bundle
  , module Snarky.Backend.Kimchi.Proof
  ) where

import Pickles.Sideload.Bundle (Bundle, mkBundle, verifierIndex)
import Snarky.Backend.Kimchi.Proof (vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson, vestaVerifierIndexToSerdeJson)
