-- | Public API for Pickles side-loading: runtime-supplied wrap
-- | verification keys + the kimchi FFI for loading them from JSON.
-- |
-- | This module is a thin re-export facade. Consumers should
-- | `import Pickles.Sideload` rather than reaching into
-- | `Pickles.Sideload.Bundle` / `Snarky.Backend.Kimchi.Proof` directly.
-- | Internal side-loading machinery
-- | (`Pickles.Sideload.{Advice,VerificationKey}`) is not re-exported.
module Pickles.Sideload
  ( module Pickles.Sideload.Bundle
  , module Snarky.Backend.Kimchi.Proof
  ) where

import Pickles.Sideload.Bundle (Bundle, mkBundle, verifierIndex)
import Snarky.Backend.Kimchi.Proof (vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson, vestaVerifierIndexToSerdeJson)
