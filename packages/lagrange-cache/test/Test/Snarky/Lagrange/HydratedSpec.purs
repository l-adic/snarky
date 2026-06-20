-- | Tests for the hydrate/flush cache (`Snarky.Lagrange.Cache.Hydrated`) over a
-- | memory-backed durable store (no browser): hydrated entries serve
-- | synchronously, `put` is sync-visible, and persists back fire-and-forget. Pure
-- | map plumbing — no kimchi.
module Test.Snarky.Lagrange.HydratedSpec
  ( spec
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (isJust, isNothing)
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (Aff, delay)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Lagrange.Cache (keyString)
import Snarky.Lagrange.Cache.Hydrated (hydratedCache)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

foreign import mkBytes :: Int -> Uint8Array

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Lagrange.Cache.Hydrated (hydrate/flush)" do
  it "serves hydrated entries synchronously, and `put` is sync-visible + persists fire-and-forget" do
    let
      k1 = { curve: "vesta", srsHash: "deadbeef", log2: 13 }
      k2 = { curve: "vesta", srsHash: "deadbeef", log2: 14 }
    durable <- liftEffect $ Ref.new (Map.singleton (keyString k1) (mkBytes 4) :: Map String Uint8Array)

    cache <- hydratedCache
      { loadAll: liftEffect (Ref.read durable)
      , putAsync: \k v -> liftEffect (Ref.modify_ (Map.insert k v) durable)
      }

    h0 <- liftEffect $ cache.get k1
    isJust h0 `shouldEqual` true
    m0 <- liftEffect $ cache.get k2
    isNothing m0 `shouldEqual` true

    liftEffect $ cache.put k2 (mkBytes 8)
    g1 <- liftEffect $ cache.get k2
    isJust g1 `shouldEqual` true

    delay (Milliseconds 20.0)
    persisted <- liftEffect $ Map.member (keyString k2) <$> Ref.read durable
    persisted `shouldEqual` true
