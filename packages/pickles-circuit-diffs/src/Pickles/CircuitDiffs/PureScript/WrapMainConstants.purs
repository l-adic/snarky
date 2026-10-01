-- | The constants a `wrap_main_*` circuit bakes in, as its comparison dump
-- | carries them: per branch its slot count, step domain, step key (whole, as
-- | the proof cache stores it) and the Lagrange bases each packed public-input
-- | scalar reads; the blinding `h`, the wrap domain pins, the slot widths and
-- | the padding challenges.
module Pickles.CircuitDiffs.PureScript.WrapMainConstants
  ( wrapMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Foldable (for_)
import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.PureScript.Common (DerivedKey, srsLagrangeAt, stepKeyExport)
import Pickles.CircuitDiffs.Types (Constants(..), Point)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.Main (WrapMainConfig)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, sizeInFields)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The constants. `keys` are the branches' step keys, derived over `srs`;
-- | each branch's Lagrange table must be `srs`'s Lagrange commitments on its
-- | key's domain, or this throws. The table is exported at every scalar of the
-- | packed step statement of `mpv` slots (`PackedStepPublicInput`).
wrapMainConstants
  :: forall branches mpv stepChunks
   . Reflectable branches Int
  => CircuitType WrapField
       (PackedStepPublicInput mpv WrapIPARounds (F WrapField) Boolean)
       (PackedStepPublicInput mpv WrapIPARounds (FVar WrapField) (BoolVar WrapField))
  => WrapMainConfig branches mpv stepChunks
  -> CRS VestaG
  -> Vector branches (DerivedKey VestaG StepField)
  -> Vector mpv Int
  -> Effect Constants
wrapMainConstants config srs keys slotWidths = do
  for_ (Array.range 0 (packedCount - 1)) \i ->
    for_ (Vector.toUnfoldable (Vector.zip keys (config.lagrangeTable i)) :: Array _) \(key /\ table) ->
      unless (Vector.toUnfoldable table == srsLagrangeAt srs key.domainLog2 i)
        $ throw
        $ "wrap_main: Lagrange base " <> show i
            <> " is not the SRS's on its step key's domain 2^"
            <> show key.domainLog2
  pure $ WrapMain
    { h: fPtJson config.blindingH
    , branches: Vector.toUnfoldable $ Vector.generate @branches \b ->
        branch b (Vector.index config.stepWidths b) (Vector.index config.domainLog2s b)
          (Vector.index keys b)
    , pins: map (\slots -> map (map fromEnum) (Vector.toUnfoldable slots :: Array (Maybe _)))
        (Vector.toUnfoldable config.prevWrapDomainPins :: Array _)
    , slotWidths: Vector.toUnfoldable slotWidths :: Array Int
    , dummy: map fieldJson
        (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded :: Array WrapField)
    }
  where
  -- branch `b`'s table: its column of each scalar's per-branch bases
  branch b width domainLog2 key =
    { width
    , domainLog2
    , key: stepKeyExport key.verifierIndex
    , lagrange: Array.range 0 (packedCount - 1) <#> \i ->
        map fPtJson (Vector.toUnfoldable (Vector.index (config.lagrangeTable i) b) :: Array _)
    }

  packedCount = sizeInFields (Proxy @WrapField)
    (Proxy @(PackedStepPublicInput mpv WrapIPARounds (F WrapField) Boolean))

  fieldJson :: WrapField -> String
  fieldJson = BigInt.toString <<< toBigInt

  fPtJson :: AffinePoint (F WrapField) -> Point
  fPtJson (AffinePoint { x: F x, y: F y }) = [ fieldJson x, fieldJson y ]
