-- | The constants a `step_main_*` circuit bakes in, as JSON for the Lean
-- | `check_cs` harness: what `Pickles.Step.Main.stepMain` takes beyond the
-- | rule. The statement width `mpv`, the blinding `h`, and per slot, in the
-- | rule's order: its source (`self` or `external`), width, chunk count,
-- | candidate step domains, the Lagrange bases its public-input commitment
-- | reads, and an external slot's wrap key. Every value is written by its
-- | own `WriteForeign` instance.
module Pickles.CircuitDiffs.PureScript.StepMainConstants
  ( stepMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof (PackedWrapStatement)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (SlotVkBlueprint(..), StepMainSrsData)
import Pickles.Types (StepIPARounds, WrapVkChunks)
import Simple.JSON (writeJSON)
import Snarky.Circuit.DSL (F, sizeInFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | The constants as JSON. `widths` are the prevs spec's slot widths; a
-- | side-loaded slot is `side_loaded`, with neither Lagrange bases nor key.
stepMainConstants
  :: forall len. Int -> Vector len Int -> StepMainSrsData len -> String
stepMainConstants mpv widths srsData =
  writeJSON
    { mpv
    , blindingH: srsData.blindingH
    , slots:
        Vector.toUnfoldable
          ( Vector.zipWith ($)
              ( Vector.zipWith ($)
                  (Vector.zipWith slot widths srsData.perSlotNumChunks)
                  srsData.perSlotFopDomainLog2s
              )
              srsData.perSlotVkBlueprints
          ) :: Array _
    }
  where
  slot width numChunks domainLog2s blueprint =
    let
      src = case blueprint of
        BlueprintSelf lagrange -> { source: "self", lagrange: bases lagrange, key: Nothing }
        BlueprintExternal lagrange vk ->
          { source: "external", lagrange: bases lagrange, key: Just vk }
        BlueprintSideLoaded _ -> { source: "side_loaded", lagrange: [], key: Nothing }
    in
      { source: src.source
      , width
      , numChunks
      , domainLog2s: NEA.toArray domainLog2s
      , lagrange: src.lagrange
      , key: src.key
      }

  -- the public-input commitment reads one base per scalar of the packed
  -- wrap statement
  lagrangeCount = sizeInFields (Proxy @StepField)
    (Proxy @(PackedWrapStatement StepIPARounds (F StepField) (Type1 (F StepField))))

  bases
    :: LagrangeBaseLookup WrapVkChunks StepField
    -> Array (Vector WrapVkChunks (AffinePoint (F StepField)))
  bases lagrange = Array.range 0 (lagrangeCount - 1) <#> \i -> (lagrange i).constant
