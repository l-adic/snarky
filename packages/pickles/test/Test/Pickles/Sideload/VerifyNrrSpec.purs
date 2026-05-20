-- | End-to-end verify of an OCaml-produced NRR wrap proof. Loads the
-- | NRR fixture (`vk + kimchi proof + statement + wrapping`), builds
-- | a `Verifier`, and runs `verifyOcamlProof`. Asserts the result is
-- | `true`.
-- |
-- | Strongest cross-stack compatibility check: PS's verifier accepts
-- | an OCaml-produced wrap proof against an OCaml-produced VK, given
-- | correctly decoded deferred-values + message digests + AllEvals.
-- |
-- | DEFERRED — `Pickles.Sideload.FFI` still routes through
-- | `snarky-crypto`'s Rust-side serde (`vestaProofFromSerdeJson`,
-- | `vestaVerifierIndexFromSerdeJson`, …). After the kimchi-napi
-- | migration in slices 3.3/3.4 the rest of the prover values carry
-- | the kimchi-napi tag while the sideload-loaded ones still carry the
-- | snarky-crypto tag, so any boundary call fails with "Failed to get
-- | external value". The body below is preserved verbatim and will be
-- | re-wired into the spec by switching `pending` back to `it` once the
-- | slice 3.5 sideload-serde port lands.
module Test.Pickles.Sideload.VerifyNrrSpec
  ( spec
  -- Preserved test body; restore by swapping `pending` for
  -- `it "<name>" _verifyNrrBody` once the deferred work lands.
  , _verifyNrrBody
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles (mkVerifier)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture, verifyOcamlProof)
import Test.Spec (SpecT, describe, pending)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff SharedSrs Aff Unit
spec = describe "Pickles.Sideload.NRR verify" do
  pending "verifyOcamlProof accepts the OCaml-produced NRR wrap proof (deferred: slice 3.5 sideload serde)"

-- | Preserved body for the deferred spec above. Underscore prefix
-- | silences the unused-name warning. Restore by replacing `pending` with
-- | `it "<name>" _verifyNrrBody` and dropping the underscore.
_verifyNrrBody :: SharedSrs -> Aff Unit
_verifyNrrBody { pallasSrs, vestaSrs } = do
  fixture <- loadNrrFixture { pallasSrs, vestaSrs } "packages/pickles/test/fixtures/sideload/nrr"
  let
    OcamlProof p = fixture.ocamlProof
    verifier = mkVerifier
      { wrapVK: fixture.vk
      , vestaSrs: fixture.vestaSrs
      , stepDomainLog2: p.stepDomainLog2
      , stepNumChunks: 1
      }
  verifyOcamlProof verifier fixture.ocamlProof `shouldEqual` true
