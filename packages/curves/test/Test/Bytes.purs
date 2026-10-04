module Test.Snarky.Curves.Bytes where

import Prelude

import Data.Foldable (foldMap)
import Effect.Class (liftEffect)
import JS.BigInt (BigInt)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, toBigInt, toHexLe)
import Test.QuickCheck (quickCheck, (===))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy)

-- | `pasta-runtime`'s flat encoding of an array, the layout kimchi-napi
-- | takes a witness column in, as hex.
foreign import flatHexLe :: Array BigInt -> String

spec :: forall f. PrimeField f => SerdeHex f => Proxy f -> Spec Unit
spec _ = describe "flat byte encoding" do
  it "is each element's 32 little-endian bytes, in order" $ liftEffect $
    quickCheck \(xs :: Array f) ->
      flatHexLe (map toBigInt xs) === foldMap toHexLe xs

  it "encodes the extreme elements" do
    let xs = [ zero, one, negate one ] :: Array f
    flatHexLe (map toBigInt xs) `shouldEqual` foldMap toHexLe xs
