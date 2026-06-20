-- | The browser self-prover entry for `prover.js`: open the shared IndexedDB
-- | Lagrange cache and build the prover through it, handed back as a `Promise` so
-- | the JS worker can `await` it. Compile warms the bases through the synchronous
-- | hydrate/flush view of the DB (the compile runs in this Web Worker, so the
-- | synchronous warm is worker-isolated and never blocks the UI thread), and they
-- | persist across reloads and to the other same-origin workers.
module Snarky.Example.Web.Prover
  ( buildBrowserProver
  ) where

import Prelude

import Control.Promise (Promise, fromAff)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Types (Payload)
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.SrsCache (idbLagrangeCache)

buildBrowserProver
  :: Logger
  -> { chain :: String, depth :: Int }
  -> Effect (Promise (Payload -> Effect Payload))
buildBrowserProver logger args = fromAff do
  lagrangeCache <- idbLagrangeCache logger
  buildProver (Just lagrangeCache) logger args
