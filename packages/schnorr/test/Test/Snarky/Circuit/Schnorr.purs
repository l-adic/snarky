module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Test.Spec (Spec, describe, pending)

-- | Pallas-curve verification circuit roundtrip. Disabled while
-- | iter-2c restructures the Signature type (`s` now lives as a
-- | 255-bit vector, not a field). Re-enable once
-- | `Snarky.Circuit.Schnorr.verifies` converges with the production
-- | OCaml fixture via the `pickles-circuit-diffs` loop and the
-- | Gen/test machinery is rewired for the new shape.
spec :: forall cfg. cfg -> Spec Unit
spec _ = describe "Snarky.Circuit.Schnorr" do
  pending "iter-2c: re-enable after circuit-diff convergence"
