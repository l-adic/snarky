-- | `self.postMessage` of a pre-encoded wire object, shared by the prover
-- | worker's entry (`Worker`) and its logger (`WorkerLog`) — both run inside a
-- | worker and post `WorkerMsg`-encoded objects to their host.
module Snarky.Example.Web.P2P.Post
  ( post
  ) where

import Prelude

import Effect (Effect)
import Foreign (Foreign)

foreign import post :: Foreign -> Effect Unit
