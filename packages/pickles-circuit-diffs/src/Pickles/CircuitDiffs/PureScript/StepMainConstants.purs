-- | The constants a `step_main_*` circuit bakes in, as its comparison dump
-- | carries them: what `Pickles.Step.Main.stepMain` takes beyond the rule. The
-- | blinding `h`, and per slot, in the rule's order, by its source (self,
-- | external or side-loaded): its width, chunk count and candidate step
-- | domains, and for a self or external slot the Lagrange bases its
-- | public-input commitment reads and the wrap key it verifies against
-- | (whole, as the proof cache stores it).
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
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.PureScript.Common (DerivedKey, KeyExport, srsLagrangeAt, wrapKeyExport)
import Pickles.CircuitDiffs.Types (Chunked, Constants(..), Point, StepSlot(..))
import Pickles.Field (StepField, WrapField)
import Pickles.IncrementallyVerifyProof (PackedWrapStatement)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (SlotVkBlueprint(..), StepMainSrsData)
import Pickles.Types (StepIPARounds, WrapVkChunks)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), sizeInFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The constants. `widths` are the prevs spec's slot widths and `keys` each
-- | slot's wrap key, derived over `srs`; a side-loaded slot has none. A self
-- | or external slot's Lagrange table must be `srs`'s Lagrange commitments on
-- | its key's domain, or this throws.
stepMainConstants
  :: forall len
   . Vector len Int
  -> StepMainSrsData len
  -> CRS PallasG
  -> Vector len (Maybe (DerivedKey PallasG WrapField))
  -> Effect Constants
stepMainConstants widths srsData srs keys = do
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
  pure $ StepMain { h: point srsData.blindingH, slots }
  where
  slot (((width /\ numChunks) /\ domainLog2s) /\ (blueprint /\ key)) =
    let
      domains = NEA.toArray domainLog2s
    in
      case blueprint, key of
        BlueprintSelf lagrange, Just k -> do
          checkTable k lagrange
          pure $ SelfSlot { width, numChunks, domains, key: export k, lagrange: bases lagrange }
        BlueprintExternal lagrange _, Just k -> do
          checkTable k lagrange
          pure $ ExternalSlot { width, numChunks, domains, key: export k, lagrange: bases lagrange }
        BlueprintSideLoaded _, Nothing ->
          pure $ SideLoadedSlot { width, numChunks, domains }
        _, _ -> throw "step_main: a self or external slot needs its wrap key, a side-loaded one none"

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

  bases :: LagrangeBaseLookup WrapVkChunks StepField -> Array Chunked
  bases lagrange = Array.range 0 (lagrangeCount - 1) <#> \i ->
    map point (Vector.toUnfoldable (lagrange i).constant :: Array _)

  point :: AffinePoint (F StepField) -> Point
  point (AffinePoint { x: F x, y: F y }) =
    [ BigInt.toString (toBigInt x), BigInt.toString (toBigInt y) ]
