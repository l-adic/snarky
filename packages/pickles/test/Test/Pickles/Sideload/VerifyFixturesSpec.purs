-- | End-to-end verify of OCaml-produced wrap proofs across the
-- | max_proofs_verified coverage matrix, exercising the generalized
-- | `Test.Pickles.Sideload.Loader` (which rebuilds the prev-proof message
-- | digests + `oldBulletproofChallenges` from the carried statement data):
-- |
-- |   * simple_chain      — mpv = 1, nc = 1  (one self-recursive prev; b0/b1/b2)
-- |   * tree_proof_return — mpv = 2, nc = 1  (heterogeneous prevs: NRR external
-- |                         slot + self-recursive slot; b0/b1/b2)
-- |
-- | (NRR — mpv = 0, nc = 1 — is covered by `VerifyNrrSpec`.) Each loads via
-- | `loadFixture` with the single-field statement codec
-- | (`decodeHex` + `\f -> [f]`) and asserts the canonical verify accepts it —
-- | exercising the loader's full mpv = 0/1/2 generality at nc = 1.
-- |
-- | NOTE on num_chunks > 1 (chunks2 was dropped from this matrix): a
-- | serialized chunked proof CANNOT be verified from the standard Pickles
-- | wire form. `Proof.to_repr` (`proof.ml:260`) serializes the prev-proof
-- | public-input evaluation as `(x1.(0), x2.(0))` — only chunk 0 — but the
-- | verifier's `combined_inner_product` (`wrap.ml:38,53` →
-- | `Pcs_batch.combine_split_evaluations`) needs every nc chunk. We verified
-- | this is an OCaml-side limitation, not a loader bug: OCaml's *own*
-- | `Proof.verify` fails (`dlog_check`) on a chunked proof after a
-- | `to_repr → of_repr` round-trip. `public_input_skeleton.json` is exactly that lossy
-- | form (`to_yojson_full`), so the missing chunk simply isn't in the
-- | fixture. Supporting nc > 1 would require the dumper to export the full
-- | in-memory `prev_evals` (whose own yojson preserves all chunks); until
-- | then the loader is exercised only on nc = 1 fixtures.
module Test.Pickles.Sideload.VerifyFixturesSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Pickles.Verify (verifyStages)
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
  -- N=2, heterogeneous prevs: slot 0 = NRR (external), slot 1 = self-recursive
  -- Tree proof (dummy N2 in b0, real prior Tree proof in b1/b2).
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
