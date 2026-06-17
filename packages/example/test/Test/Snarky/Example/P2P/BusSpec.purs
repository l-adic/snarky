-- | Sanity checks for the in-memory bus + the `Transport.fromImpl` FFI it builds
-- | on: broadcast vs targeted send, peer discovery (both directions), and that a
-- | disconnected node goes inert. These underpin the coordination scenario tests.
module Test.Snarky.Example.P2P.BusSpec
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Example.P2P.Transport (broadcast, onMessage, onPeer, sendTo)
import Snarky.Example.P2P.Types (Frame(..), PeerId(..))
import Test.Snarky.Example.P2P.InMemoryBus (connect, disconnect, newBus)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "In-memory transport bus" do
  it "delivers broadcasts to every other node, not the sender" do
    bus <- liftEffect newBus
    a <- liftEffect (connect bus "a")
    b <- liftEffect (connect bus "b")
    c <- liftEffect (connect bus "c")
    inA <- liftEffect (Ref.new [])
    inB <- liftEffect (Ref.new [])
    inC <- liftEffect (Ref.new [])
    liftEffect $ onMessage a \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inA
    liftEffect $ onMessage b \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inB
    liftEffect $ onMessage c \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inC
    liftEffect (broadcast b (Frame "hi"))
    liftEffect (Ref.read inA) >>= \x -> x `shouldEqual` [ Tuple (PeerId "b") (Frame "hi") ]
    liftEffect (Ref.read inC) >>= \x -> x `shouldEqual` [ Tuple (PeerId "b") (Frame "hi") ]
    liftEffect (Ref.read inB) >>= \x -> x `shouldEqual` [] -- not the sender

  it "delivers a targeted sendTo only to the addressed node" do
    bus <- liftEffect newBus
    a <- liftEffect (connect bus "a")
    b <- liftEffect (connect bus "b")
    c <- liftEffect (connect bus "c")
    inA <- liftEffect (Ref.new [])
    inC <- liftEffect (Ref.new [])
    liftEffect $ onMessage a \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inA
    liftEffect $ onMessage c \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inC
    liftEffect (sendTo b (PeerId "a") (Frame "yo"))
    liftEffect (Ref.read inA) >>= \x -> x `shouldEqual` [ Tuple (PeerId "b") (Frame "yo") ]
    liftEffect (Ref.read inC) >>= \x -> x `shouldEqual` []

  it "fires onPeer both ways: existing learns of newcomer, newcomer replays existing" do
    bus <- liftEffect newBus
    a <- liftEffect (connect bus "a")
    seenByA <- liftEffect (Ref.new [])
    liftEffect $ onPeer a \id -> Ref.modify_ (\xs -> Array.snoc xs id) seenByA
    -- b joins after a; a should be told about b
    b <- liftEffect (connect bus "b")
    seenByB <- liftEffect (Ref.new [])
    liftEffect $ onPeer b \id -> Ref.modify_ (\xs -> Array.snoc xs id) seenByB
    liftEffect (Ref.read seenByA) >>= \x -> x `shouldEqual` [ PeerId "b" ]
    -- b registers onPeer after connecting; it replays the already-present a
    liftEffect (Ref.read seenByB) >>= \x -> x `shouldEqual` [ PeerId "a" ]

  it "makes a disconnected node inert (no receive, no send)" do
    bus <- liftEffect newBus
    a <- liftEffect (connect bus "a")
    b <- liftEffect (connect bus "b")
    c <- liftEffect (connect bus "c")
    inA <- liftEffect (Ref.new [])
    inC <- liftEffect (Ref.new [])
    liftEffect $ onMessage a \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inA
    liftEffect $ onMessage c \from msg -> Ref.modify_ (\xs -> Array.snoc xs (Tuple from msg)) inC
    liftEffect (disconnect bus "a")
    -- a no longer receives b's broadcast…
    liftEffect (broadcast b (Frame "one"))
    liftEffect (Ref.read inA) >>= \x -> x `shouldEqual` []
    liftEffect (Ref.read inC) >>= \x -> x `shouldEqual` [ Tuple (PeerId "b") (Frame "one") ]
    -- …and a can no longer send
    liftEffect (broadcast a (Frame "two"))
    liftEffect (Ref.read inC) >>= \x -> x `shouldEqual` [ Tuple (PeerId "b") (Frame "one") ]
