-- | The constants a `step_main_*` circuit bakes in, as JSON for the Lean
-- | `check_cs` harness: what `Pickles.Step.Main.stepMain` takes beyond the
-- | rule. The statement width `mpv`, the blinding `h`, and per slot, in the
-- | rule's order: its source (`self` or `external`), width, chunk count,
-- | candidate step domains, the Lagrange bases its public-input commitment
-- | reads, and the wrap key it verifies against (whole, as the proof cache
-- | stores it). Every value is written by its own `WriteForeign` instance.
module Pickles.CircuitDiffs.PureScript.StepMainConstants
  ( stepMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.CircuitDiffs.PureScript.Common (DerivedKey, KeyExport, srsLagrangeAt, wrapKeyExport)
import Pickles.Field (StepField, WrapField)
import Pickles.IncrementallyVerifyProof (PackedWrapStatement)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (SlotVkBlueprint(..), StepMainSrsData)
import Pickles.Types (StepIPARounds, WrapVkChunks)
import Simple.JSON (writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F, sizeInFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | The constants as JSON. `widths` are the prevs spec's slot widths and
-- | `keys` each slot's wrap key, derived over `srs`; a side-loaded slot is
-- | `side_loaded`, with neither Lagrange bases nor key. A self or external
-- | slot's Lagrange table must be `srs`'s Lagrange commitments on its key's
-- | domain, or this throws before anything is written.
stepMainConstants
  :: forall len
   . Int
  -> Vector len Int
  -> StepMainSrsData len
  -> CRS PallasG
  -> Vector len (Maybe (DerivedKey PallasG WrapField))
  -> Effect String
stepMainConstants mpv widths srsData srs keys = do
  slots <- traverse slot
    ( Vector.toUnfoldable
        ( Vector.zipWith (/\)
            ( Vector.zipWith (/\)
                (Vector.zipWith (/\) widths srsData.perSlotNumChunks)
                srsData.perSlotFopDomainLog2s
            )
            (Vector.zipWith (/\) srsData.perSlotVkBlueprints keys)
        ) :: Array _
    )
  pure $ writeJSON { mpv, blindingH: srsData.blindingH, slots }
  where
  slot (((width /\ numChunks) /\ domainLog2s) /\ (blueprint /\ key)) = do
    src <- case blueprint, key of
      BlueprintSelf lagrange, Just k -> do
        checkTable k lagrange
        pure { source: "self", lagrange: bases lagrange, key: Just (export k) }
      BlueprintExternal lagrange _, Just k -> do
        checkTable k lagrange
        pure { source: "external", lagrange: bases lagrange, key: Just (export k) }
      BlueprintSideLoaded _, Nothing ->
        pure { source: "side_loaded", lagrange: [], key: Nothing }
      _, _ -> throw "step_main: a self or external slot needs its wrap key, a side-loaded one none"
    pure
      { source: src.source
      , width
      , numChunks
      , domainLog2s: NEA.toArray domainLog2s
      , lagrange: src.lagrange
      , key: src.key
      }

  export :: DerivedKey PallasG WrapField -> KeyExport
  export k = wrapKeyExport k.verifierIndex

  checkTable
    :: DerivedKey PallasG WrapField -> LagrangeBaseLookup WrapVkChunks StepField -> Effect Unit
  checkTable k lagrange =
    for_ (Array.range 0 (lagrangeCount - 1)) \i ->
      unless (Vector.toUnfoldable (lagrange i).constant == srsLagrangeAt srs k.domainLog2 i)
        $ throw
        $ "step_main: Lagrange base " <> show i
            <> " is not the SRS's on its wrap key's domain 2^"
            <> show k.domainLog2

  -- the public-input commitment reads one base per scalar of the packed
  -- wrap statement
  lagrangeCount = sizeInFields (Proxy @StepField)
    (Proxy @(PackedWrapStatement StepIPARounds (F StepField) (Type1 (F StepField))))

  bases
    :: LagrangeBaseLookup WrapVkChunks StepField
    -> Array (Vector WrapVkChunks (AffinePoint (F StepField)))
  bases lagrange = Array.range 0 (lagrangeCount - 1) <#> \i -> (lagrange i).constant
