-- | Main-thread handle to the prover worker (`P2P.ProverService`): a tiny
-- | request/response RPC over `postMessage`, surfaced as `Aff` calls. The main
-- | thread (transport + gossip) only ever moves opaque proof `String`s; all
-- | crypto + codec work happens in the worker.
module Snarky.Example.P2P.ProverClient
  ( Client
  , LeafOut
  , SeedOut
  , BlockMeta
  , MergeOut
  , mkClient
  , onEvent
  , initService
  , seedBlock
  , genBlock
  , proveBaseLeaf
  , merge
  , verify
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Foreign (Foreign)
import Web.Worker.Worker (Worker)

foreign import data Client :: Type

type LeafOut = { slot :: Int, key :: String, wire :: String }

type SeedOut =
  { n :: Int
  , leaves :: Array LeafOut
  , leafStmts :: Array { slot :: Int, stmt :: String }
  }

type MergeOut = { key :: String, wire :: String }

type BlockMeta = { n :: Int, leafStmts :: Array { slot :: Int, stmt :: String } }

-- | Wrap a worker as an RPC client (installs its `onmessage` dispatcher).
foreign import mkClient :: Worker -> Effect Client

-- | Subscribe to the worker's non-RPC events (log/status lines).
foreign import onEvent :: Client -> (Foreign -> Effect Unit) -> Effect Unit

foreign import _init :: Client -> EffectFnAff { fingerprint :: String }
foreign import _seed :: Client -> EffectFnAff SeedOut
foreign import _genBlock :: Client -> EffectFnAff BlockMeta
foreign import _proveLeaf :: Client -> Int -> EffectFnAff LeafOut
foreign import _merge :: Client -> { aWire :: String, bWire :: String } -> EffectFnAff MergeOut
foreign import _verify :: Client -> String -> EffectFnAff Boolean

-- | Boot the worker (compile circuit + warm SRS); resolves to the fingerprint.
initService :: Client -> Aff String
initService c = _.fingerprint <$> fromEffectFnAff (_init c)

seedBlock :: Client -> Aff SeedOut
seedBlock c = fromEffectFnAff (_seed c)

-- | Generate the block (stashes its jobs in the worker); returns the public shape.
genBlock :: Client -> Aff BlockMeta
genBlock c = fromEffectFnAff (_genBlock c)

-- | Prove the j-th base leaf of the stashed block.
proveBaseLeaf :: Client -> Int -> Aff LeafOut
proveBaseLeaf c j = fromEffectFnAff (_proveLeaf c j)

merge :: Client -> { aWire :: String, bWire :: String } -> Aff MergeOut
merge c p = fromEffectFnAff (_merge c p)

verify :: Client -> String -> Aff Boolean
verify c w = fromEffectFnAff (_verify c w)
