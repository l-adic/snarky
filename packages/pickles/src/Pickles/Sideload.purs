-- | Public API for Pickles side-loading: runtime-supplied wrap
-- | verification keys + the kimchi FFI for loading them from JSON.
-- |
-- | This module is a thin re-export facade. Consumers should
-- | `import Pickles.Sideload` rather than reaching into
-- | `Pickles.Sideload.Bundle` / `Pickles.Sideload.FFI` directly.
-- | Internal side-loading machinery
-- | (`Pickles.Sideload.{Advice,VerificationKey}`) is not re-exported.
module Pickles.Sideload
  ( module Pickles.Sideload.Bundle
  , module Pickles.Sideload.FFI
  ) where

import Pickles.Sideload.Bundle (Bundle, mkBundle, verifierIndex)
import Pickles.Sideload.FFI (VkFeatureFlags, noOptionalFeatures, vestaHydrateVerifierIndex, vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson, vestaVerifierIndexToSerdeJson)
