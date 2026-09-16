-- | Verifies OCaml-produced wrap proofs across the
-- | `max_proofs_verified` matrix: three `simple_chain` proofs at mpv 1
-- | (one self-recursive prev) and three `tree_proof_return` proofs at
-- | mpv 2 (heterogeneous prevs). mpv 0 is covered by `VerifyNrrSpec`.
-- |
-- | Each fixture must verify, and the accumulator list the verifier
-- | rebuilds from the carried messages must be the one the prover
-- | stored in the proof.
-- |
-- | Every fixture here has `num_chunks = 1`. The dumped wire form keeps
-- | only chunk 0 of the prev-proof public-input evaluation while
-- | `combined_inner_product` needs every chunk — OCaml's own verifier
-- | fails the same way on a chunked proof round-tripped through it — so
-- | covering `num_chunks > 1` needs a dumper that exports the full
-- | in-memory `prev_evals`.
module Test.Pickles.Sideload.VerifyFixturesSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Pickles.Verify (verifyStages, wrapAccumulators)
import Snarky.Backend.Kimchi.Proof (proofPrevChallenges)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (decodeHex, loadFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.VerifyFixtures (mpv)" do
  it "verifies simple_chain b0 (mpv=1, base case)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/simple_chain/wrap0")
  it "verifies simple_chain b1 (mpv=1)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/simple_chain/wrap1")
  it "verifies simple_chain b2 (mpv=1)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/simple_chain/wrap2")
  -- Slot 0 is an external NRR proof; slot 1 is a dummy in b0 and the
  -- prior tree proof in b1 and b2.
  it "verifies tree_proof_return b0 (mpv=2, base case)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/tree_proof_return/wrap0")
  it "verifies tree_proof_return b1 (mpv=2)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/tree_proof_return/wrap1")
  it "verifies tree_proof_return b2 (mpv=2)"
    (liftAff <<< verifyDir "packages/pickles/test/fixtures/tree_proof_return/wrap2")
  where
  verifyDir :: String -> SharedSrs -> Aff Unit
  verifyDir dir { pallasSrs, vestaSrs } = do
    fixture <- loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs } dir
    verifyStages fixture.verifier fixture.verifiableProof
      `shouldEqual` { accumulatorOk: true, kimchiOk: true }
    wrapAccumulators fixture.verifier fixture.verifiableProof
      `shouldEqual` proofPrevChallenges fixture.verifiableProof.wrapProof
