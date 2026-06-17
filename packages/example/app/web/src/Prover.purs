-- | The browser self-prover entry for `prover.js`: open the shared IndexedDB SRS
-- | cache and build the prover through it, handed back as a `Promise` so the JS
-- | worker can `await` it. The cache is the same same-origin DB the engine warms,
-- | so on a warm cache this prover injects the Lagrange bases instead of FFTing
-- | (and its hits/misses log as "[self] [srs-cache] …").
module Snarky.Example.Web.Prover
  ( buildBrowserProver
  ) where

import Prelude

import Control.Promise (Promise, fromAff)
import Effect (Effect)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Types (Payload)
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.SrsCache (openSrsCache)

buildBrowserProver
  :: Logger
  -> { chain :: String, depth :: Int }
  -> Effect (Promise (Payload -> Effect Payload))
buildBrowserProver logger args = fromAff do
  cache <- openSrsCache logger
  buildProver cache logger args
