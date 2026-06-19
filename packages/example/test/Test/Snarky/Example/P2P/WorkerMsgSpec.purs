-- | Round-trip tests for the worker↔main wire protocol
-- | (`Snarky.Example.P2P.WorkerMsg`). Pure `Foreign` codecs, so they run in Node:
-- | every message variant must survive `encode` → `decode`, and malformed /
-- | unknown shapes must decode to `Nothing` (dropped, never crash).
module Test.Snarky.Example.P2P.WorkerMsgSpec
  ( spec
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Foreign (unsafeToForeign)
import Snarky.Example.P2P.Types (Frame(..), PeerId(..))
import Snarky.Example.P2P.WorkerMsg (WorkerMsg(..), decodeWorkerMsg, encodeWorkerMsg)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

roundTrips :: WorkerMsg -> Aff Unit
roundTrips m = decodeWorkerMsg (encodeWorkerMsg m) `shouldEqual` Just m

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Example.P2P.WorkerMsg" do
  it "round-trips the engine/peer UI events" do
    roundTrips (WLog { severity: "info", text: "compiling circuit" })
    roundTrips (WPhase "proving (base + merge)")
    roundTrips
      ( WScan
          { blockId: 0
          , leaves: 8
          , statuses: [ { slot: 1, status: "complete" }, { slot: 2, status: "pending" } ]
          }
      )
    roundTrips (WVerified true)
    roundTrips (WVerified false)
    roundTrips
      ( WPeers
          [ { id: "p1", status: "idle", busy: false, completed: 0 }
          , { id: "p2", status: "proving merge", busy: true, completed: 3 }
          ]
      )

  it "round-trips the transport relay messages" do
    roundTrips (WBroadcast (Frame "{\"tag\":\"Join\"}"))
    roundTrips (WSend (PeerId "peer-7") (Frame "an encoded frame"))

  it "drops an unknown tag or a malformed envelope" do
    decodeWorkerMsg (unsafeToForeign { tag: "bogus", value: 1 }) `shouldEqual` Nothing
    decodeWorkerMsg (unsafeToForeign { nonsense: true }) `shouldEqual` Nothing
    -- a "scan" event whose value isn't a ScanView
    decodeWorkerMsg (unsafeToForeign { tag: "scan", value: "not a scan" }) `shouldEqual` Nothing
