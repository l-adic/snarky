-- | Server-side merger for the privacy split (client base-proves, server
-- | merges). Compiled once at startup (`initServer`); each request reconstructs
-- | the client's base proofs and reduces the merge tree to a verified root
-- | (`serverMerge`). The server only ever sees the public proofs + ledger-root
-- | statements — never the clients' private transaction witnesses.
-- |
-- | Both functions are JS-callable (callback init, synchronous per-request
-- | merge); driven by merge-server.cjs.
module Snarky.Example.MergeServer
  ( ServerState
  , initServer
  , serverMerge
  ) where

import Prelude

import Colog (richMessageStdout)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (attempt, launchAff_)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import Mina.ChainId (ChainId(..))
import Pickles (toVerifiable, verifyBatch)
import Pickles.Prove.SerializeProof (WidthDummies, toSerializableCompiledProof)
import Snarky.Example.Env (Env, mkConfig, mkEnv)
import Snarky.Example.Merge (Depth, decodeNode, mergeTree, mkWidthDummies, slotStatements)
import Snarky.Example.Snark.LeafCodec (encodeLeaf)

type ServerState = { env :: Env Depth, dummies :: WidthDummies }

-- | Compile once. Callback style so JS can wrap it in a Promise.
initServer :: (ServerState -> Effect Unit) -> (String -> Effect Unit) -> Effect Unit
initServer onReady onError = launchAff_ do
  let logger = richMessageStdout
  res <- attempt do
    -- Native backend (node default): the rayon pool needs no explicit init.
    config <- liftEffect $ mkConfig Testnet
    env <- liftEffect $ mkEnv @Depth logger config
    pure { env, dummies: mkWidthDummies config.pallasSrs config.vestaSrs }
  liftEffect $ case res of
    Right st -> onReady st
    Left e -> onError (message e)

-- | Reconstruct the client's base proofs, merge to a root, verify. Synchronous
-- | (proving is CPU-bound); one request at a time is fine for the demo.
serverMerge :: ServerState -> Array String -> Effect { accepted :: Boolean, root :: String }
serverMerge { env, dummies } leafStrings = do
  leaves <- traverse (decodeNode dummies) leafStrings
  let
    n = Array.length leaves
    leafMap = Map.fromFoldable (Array.mapWithIndex (\j node -> Tuple (n + j) node) leaves)
    stmts = slotStatements n leaves
  root <- mergeTree env n stmts leafMap
  let ok = verifyBatch env.compiledTx.verifier [ toVerifiable root.proof ]
  pure { accepted: ok, root: encodeLeaf (toSerializableCompiledProof root.proof) }
