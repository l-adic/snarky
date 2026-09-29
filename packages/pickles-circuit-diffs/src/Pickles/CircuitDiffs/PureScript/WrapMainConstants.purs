-- | The constants a `wrap_main_*` circuit bakes in, as JSON for the Lean
-- | `check_cs` harness: the branches' slot counts, step domains and step
-- | keys (whole, as the proof cache stores them), the Lagrange bases each
-- | packed public-input scalar reads, the blinding `h`, the wrap domain
-- | pins, the slot widths and the padding challenges.
module Pickles.CircuitDiffs.PureScript.WrapMainConstants
  ( wrapMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Foldable (for_)
import Data.Maybe (maybe)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.PureScript.Common (DerivedKey, srsLagrangeAt, stepKeyExport)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.Main (WrapMainConfig)
import Simple.JSON (writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, sizeInFields)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The constants as JSON. `keys` are the branches' step keys, derived
-- | over `srs`; each branch's Lagrange table must be `srs`'s Lagrange
-- | commitments on its key's domain, or this throws before anything is
-- | written. The table is exported at every scalar of the packed step
-- | statement of `mpv` slots (`PackedStepPublicInput`). A side-loaded pin
-- | is `-1`.
wrapMainConstants
  :: forall branches mpv stepChunks
   . CircuitType WrapField
       (PackedStepPublicInput mpv WrapIPARounds (F WrapField) Boolean)
       (PackedStepPublicInput mpv WrapIPARounds (FVar WrapField) (BoolVar WrapField))
  => WrapMainConfig branches mpv stepChunks
  -> CRS VestaG
  -> Vector branches (DerivedKey VestaG StepField)
  -> Vector mpv Int
  -> Effect String
wrapMainConstants config srs keys slotWidths = do
  for_ (Array.range 0 (packedCount - 1)) \i ->
    for_ (Vector.toUnfoldable (Vector.zip keys (config.lagrangeTable i)) :: Array _) \(key /\ table) ->
      unless (Vector.toUnfoldable table == srsLagrangeAt srs key.domainLog2 i)
        $ throw
        $ "wrap_main: Lagrange base " <> show i
            <> " is not the SRS's on its step key's domain 2^"
            <> show key.domainLog2
  pure $ writeJSON
    { stepWidths: Vector.toUnfoldable config.stepWidths :: Array Int
    , domainLog2s: Vector.toUnfoldable config.domainLog2s :: Array Int
    , stepKeys: map (stepKeyExport <<< _.verifierIndex) (Vector.toUnfoldable keys :: Array _)
    , lagrange: Array.range 0 (packedCount - 1) <#> \i ->
        map (\chunks -> map fPtJson (Vector.toUnfoldable chunks :: Array _))
          (Vector.toUnfoldable (config.lagrangeTable i) :: Array _)
    , h: fPtJson config.blindingH
    , pins: map (\slots -> map (maybe (-1) fromEnum) (Vector.toUnfoldable slots :: Array _))
        (Vector.toUnfoldable config.prevWrapDomainPins :: Array _)
    , slotWidths: Vector.toUnfoldable slotWidths :: Array Int
    , dummyWrapExpanded: map fieldJson
        (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded :: Array WrapField)
    }
  where
  packedCount = sizeInFields (Proxy @WrapField)
    (Proxy @(PackedStepPublicInput mpv WrapIPARounds (F WrapField) Boolean))

  fieldJson :: WrapField -> String
  fieldJson = BigInt.toString <<< toBigInt

  fPtJson :: AffinePoint (F WrapField) -> Array String
  fPtJson (AffinePoint { x: F x, y: F y }) = [ fieldJson x, fieldJson y ]
