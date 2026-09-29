-- | `digestVk` against Mina's `digest_vk` of the side-loaded child key
-- | in `packages/pickles/test/fixtures/sideload_main_child/`
-- | (`vk_digest.json`, written by `dump_side_loaded_main.ml`).
-- |
-- | The key is rebuilt from the fixture's kimchi verification key with
-- | `maxProofsVerified = N0` and `actualWrapDomainSize = N0`, so the
-- | match also checks that reconstruction.
module Test.Pickles.Sideload.DigestVkSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Argonaut.Parser (jsonParser)
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)
import Pickles (ProofsVerified(..), StepField, WrapVkChunks)
import Pickles.Sideload (digestVk, mkBundle, projectVk)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (decodeHex, loadFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

fixtureDir :: String
fixtureDir = "packages/pickles/test/fixtures/sideload_main_child"

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.digestVk" do
  it "equals Mina's digest_vk of the side-loaded child key" (liftAff <<< body)
  where
  body :: SharedSrs -> Aff Unit
  body { pallasSrs, vestaSrs } = do
    fixture <- loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      fixtureDir
    digestJson <- liftEffect $ readTextFile UTF8 (fixtureDir <> "/vk_digest.json")
    expected :: StepField <- case jsonParser digestJson >>= (lmap show <<< decodeHex) of
      Right d -> pure d
      Left e -> liftEffect (Exc.throw ("vk_digest.json: " <> e))
    let
      childVk = mkBundle @WrapVkChunks
        { verifierIndex: fixture.vk
        , maxProofsVerified: N0
        , actualWrapDomainSize: N0
        }
    digestVk (projectVk childVk) `shouldEqual` expected
