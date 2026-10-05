-- | Where a prove test writes: its proof cache, under
-- | `PICKLES_PROOF_CACHE_DIR/<app>.json`, and each of its tags' dumps,
-- | under `PICKLES_DUMP_DIR/<app>/<tag>.json`. Reconstruction inputs go to
-- | `PICKLES_DUMP_DIR/<app>/shapes/<tag>.json` when dumping is on.
module Test.Pickles.Outputs
  ( AppOutputs
  , appOutputs
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import Node.Process (lookupEnv)
import Snarky.Backend.Kimchi.ProofCache (ProofCache, mkProofCache)

-- | An app's proof cache, and the dump path of each of its tags.
type AppOutputs =
  { proofCache :: Maybe ProofCache
  , dumpAt :: String -> Maybe String
  }

appOutputs :: String -> Effect AppOutputs
appOutputs app = do
  cacheDir <- lookupEnv "PICKLES_PROOF_CACHE_DIR"
  dumpDir <- lookupEnv "PICKLES_DUMP_DIR"
  pure
    { proofCache: cacheDir <#> \dir -> mkProofCache (dir <> "/" <> app <> ".json")
    , dumpAt: \tag -> dumpDir <#> \dir -> dir <> "/" <> app <> "/" <> tag <> ".json"
    }
