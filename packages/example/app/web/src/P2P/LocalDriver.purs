-- | The no-network driver: seed a block in the worker, then reduce the whole
-- | merge tree locally via the prover-RPC, and verify the root. This is both
-- | the M0 structural de-risk (proving the worker-RPC split end to end with no
-- | transport) AND the runtime "no peers connected" fallback for the P2P app.
-- |
-- | It runs the exact same readiness logic (`P2P.Dag.ready`) the gossip mesh
-- | uses, with `globalHave` collapsed to the local have-set.
module Snarky.Example.P2P.LocalDriver
  ( runLocal
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Snarky.Example.Merge (decodeStmt)
import Snarky.Example.P2P.Dag as Dag
import Snarky.Example.P2P.ProverClient (Client)
import Snarky.Example.P2P.ProverClient as RPC

type Log = { severity :: String, text :: String } -> Effect Unit

shortKey :: String -> String
shortKey = String.take 12

runLocal :: Client -> Log -> Effect Unit
runLocal client log = launchAff_ do
  fp <- RPC.initService client
  liftEffect $ log { severity: "info", text: "compiled; fingerprint " <> fp }
  seed <- RPC.seedBlock client
  liftEffect $ log { severity: "info", text: "seeded block: " <> show seed.n <> " base proofs proved locally" }

  -- leaf statements ordered by slot ascending → the DAG
  let sortedLeafStmts = Array.sortWith _.slot seed.leafStmts
  leafStmts <- liftEffect $ traverse
    ( \r -> case decodeStmt r.stmt of
        Right st -> pure st
        Left e -> throw ("bad leaf stmt: " <> show e)
    )
    sortedLeafStmts
  let dag = Dag.buildDag seed.n leafStmts

  wires <- liftEffect $ Ref.new (Map.fromFoldable (map (\l -> Tuple l.key l.wire) seed.leaves) :: Map String String)
  have <- liftEffect $ Ref.new (Set.fromFoldable (map _.key seed.leaves))

  let
    loop = do
      h <- liftEffect $ Ref.read have
      if Set.member (Dag.rootKey dag) h then pure unit
      else case Array.head (Dag.ready dag h) of
        Nothing -> liftEffect $ log { severity: "error", text: "stuck: no ready merge slot" }
        Just s -> do
          w <- liftEffect $ Ref.read wires
          let aKey = Dag.keyOf dag (2 * s)
          let bKey = Dag.keyOf dag (2 * s + 1)
          case Map.lookup aKey w, Map.lookup bKey w of
            Just aWire, Just bWire -> do
              out <- RPC.merge client { aWire, bWire }
              if out.wire == "" then
                liftEffect $ log { severity: "error", text: "merge slot " <> show s <> " rejected (child verify failed)" }
              else do
                liftEffect do
                  Ref.modify_ (Map.insert out.key out.wire) wires
                  Ref.modify_ (Set.insert out.key) have
                  log { severity: "info", text: "merged slot " <> show s <> " → " <> shortKey out.key }
                loop
            _, _ -> liftEffect $ log { severity: "error", text: "missing child wire for slot " <> show s }
  loop

  w <- liftEffect $ Ref.read wires
  case Map.lookup (Dag.rootKey dag) w of
    Just rootWire -> do
      ok <- RPC.verify client rootWire
      liftEffect $ log
        { severity: if ok then "info" else "error"
        , text: if ok then "root proof verified — block accepted ✓" else "root verification FAILED"
        }
    Nothing -> liftEffect $ log { severity: "error", text: "no root proof produced" }
