-- | Smoke test for the browser IndexedDB cache (`idbCache`), run in Node against
-- | `fake-indexeddb`. Exercises the browser-specific `_open`/`_put`/`_getAll` FFI
-- | + hydrate/flush. Load-bearing assertion: a FRESH `idbCache` over the same DB
-- | (a page reload / second worker) hydrates the entries a prior handle persisted
-- | fire-and-forget, byte payloads intact.
module Test.Snarky.Lagrange.IdbSpec
  ( spec
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (Aff, delay)
import Effect.Class (liftEffect)
import Snarky.Lagrange.Cache.Idb (idbCache)
import Test.Spec (SpecT, before_, describe, it)
import Test.Spec.Assertions (shouldEqual)

foreign import installFakeIndexedDb :: Effect Unit
foreign import mkBytes :: Int -> Uint8Array
foreign import bytesLen :: Uint8Array -> Int

spec :: SpecT Aff Unit Aff Unit
spec = before_ (liftEffect installFakeIndexedDb) $
  describe "Snarky.Lagrange.Cache.Idb (idbCache over fake-indexeddb)" do
    it "persists puts to IndexedDB; a fresh handle hydrates them" do
      let
        k1 = { curve: "vesta", srsHash: "abc123", log2: 13 }
        k2 = { curve: "pallas", srsHash: "def456", log2: 14 }

      c1 <- idbCache "lagrange-smoke"
      cold <- liftEffect $ c1.get k1
      isNothing cold `shouldEqual` true

      liftEffect $ c1.put k1 (mkBytes 4)
      liftEffect $ c1.put k2 (mkBytes 8)
      hot <- liftEffect $ c1.get k1
      isJust hot `shouldEqual` true

      delay (Milliseconds 100.0)

      -- Fresh handle over the same DB hydrates the persisted entries.
      c2 <- idbCache "lagrange-smoke"
      a <- liftEffect $ c2.get k1
      b <- liftEffect $ c2.get k2
      (bytesLen <$> a) `shouldEqual` Just 4
      (bytesLen <$> b) `shouldEqual` Just 8
