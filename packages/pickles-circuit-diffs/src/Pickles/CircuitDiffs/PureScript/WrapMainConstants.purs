-- | The constants a `wrap_main_*` circuit bakes in, as JSON for the Lean
-- | `check_cs` harness: the branches' slot counts, step domains and step
-- | keys, the Lagrange bases each packed public-input scalar reads, the
-- | blinding `h`, the wrap domain pins, the slot widths and the padding
-- | challenges.
module Pickles.CircuitDiffs.PureScript.WrapMainConstants
  ( wrapMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Maybe (maybe)
import Data.Newtype (un)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (WrapField)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.Types (WrapIPARounds)
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Main (WrapMainConfig)
import Simple.JSON (writeJSON)
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..))
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, sizeInFields)
import Snarky.Curves.Class (toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The constants as JSON. `keys` are the branches' step keys as values;
-- | the Lagrange table is exported at every scalar of the packed step
-- | statement of `mpv` slots (`PackedStepPublicInput`). A side-loaded pin
-- | is `-1`.
wrapMainConstants
  :: forall branches mpv stepChunks
   . CircuitType WrapField
       (PackedStepPublicInput mpv WrapIPARounds (F WrapField) Boolean)
       (PackedStepPublicInput mpv WrapIPARounds (FVar WrapField) (BoolVar WrapField))
  => WrapMainConfig branches mpv stepChunks
  -> Vector branches (StepVK stepChunks WrapField)
  -> Vector mpv Int
  -> String
wrapMainConstants config keys slotWidths =
  writeJSON
    { stepWidths: Vector.toUnfoldable config.stepWidths :: Array Int
    , domainLog2s: Vector.toUnfoldable config.domainLog2s :: Array Int
    , stepKeys: map keyJson (Vector.toUnfoldable keys :: Array _)
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

  ptJson :: AffinePoint WrapField -> Array String
  ptJson (AffinePoint { x, y }) = [ fieldJson x, fieldJson y ]

  fPtJson :: AffinePoint (F WrapField) -> Array String
  fPtJson (AffinePoint { x: F x, y: F y }) = [ fieldJson x, fieldJson y ]

  commJson :: ChunkedCommitment stepChunks (AffinePoint WrapField) -> Array (Array String)
  commJson c = map ptJson (Vector.toUnfoldable (un ChunkedCommitment c))

  keyJson k =
    { sigma: map commJson (Vector.toUnfoldable k.sigmaComm :: Array _)
    , coefficients: map commJson (Vector.toUnfoldable k.coefficientsComm :: Array _)
    , selectors:
        [ commJson k.genericComm
        , commJson k.psmComm
        , commJson k.completeAddComm
        , commJson k.mulComm
        , commJson k.emulComm
        , commJson k.endomulScalarComm
        ]
    }
