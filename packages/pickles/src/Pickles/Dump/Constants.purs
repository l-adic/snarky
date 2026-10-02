-- | The constants a main circuit bakes in, as a dump carries them beside
-- | its constraint system, and the keys they name, exported whole as the
-- | proof cache stores them.
-- |
-- | `stepMainConstants`: the constants a `step_main_*` circuit bakes in, as its comparison dump
-- | carries them: what `Pickles.Step.Main.stepMain` takes beyond the rule. The
-- | blinding `h`, and per slot, in the rule's order, by its source (self,
-- | external or side-loaded): its width, chunk count and candidate step
-- | domains, and for a self or external slot the Lagrange bases its
-- | public-input commitment reads and the wrap key it verifies against
-- | (whole, as the proof cache stores it).
-- |
-- | `wrapMainConstants`: the constants a `wrap_main_*` circuit bakes in, as its comparison dump
-- | carries them: per branch its slot count, step key (whole, as the proof
-- | cache stores it) and the Lagrange bases each packed public-input
-- | scalar reads; the blinding `h`, the wrap domain pins, the slot widths and
-- | the padding challenges.
module Pickles.Dump.Constants
  ( DerivedKey
  , KeyExport
  , wrapKeyExport
  , srsLagrangeAt
  , stepMainConstants
  , wrapMainConstants
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Enum (fromEnum)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.Types (Chunked, Constants(..), Point, StepSlot(..))
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.IncrementallyVerifyProof (PackedWrapStatement)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (SlotVkBlueprint(..), StepMainSrsData)
import Pickles.Types (StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (verifierIndexDigest)
import Pickles.Wrap.Main (WrapMainConfig)
import Snarky.Backend.Kimchi.Proof (class ProofFFI, srsLagrangeCommitmentChunksAt)
import Snarky.Backend.Kimchi.ProofCache (pallasVerifierIndexJsonKey, vestaVerifierIndexJsonKey)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, sizeInFields)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | A verifier index derived from a compiled circuit, with its domain's
-- | `log2`.
type DerivedKey g f = { verifierIndex :: VerifierIndex g f, domainLog2 :: Int }

-- | A key as a dump carries it for the Lean `check_cs` harness: the
-- | verifier index's JSON, as the proof cache stores it, and its digest,
-- | which the cache keys it by.
type KeyExport = { vk :: String, digest :: String }

-- | A step key, exported.
stepKeyExport :: VerifierIndex VestaG StepField -> KeyExport
stepKeyExport vk =
  { vk: pallasVerifierIndexJsonKey vk
  , digest: BigInt.toString (toBigInt (verifierIndexDigest vk))
  }

-- | A wrap key, exported.
wrapKeyExport :: VerifierIndex PallasG WrapField -> KeyExport
wrapKeyExport vk =
  { vk: vestaVerifierIndexJsonKey vk
  , digest: BigInt.toString (toBigInt (verifierIndexDigest vk))
  }

-- | The SRS's `i`-th Lagrange commitment at domain `2^log2`, every chunk,
-- | as a circuit's Lagrange table holds it. A harness checks its table
-- | against the key it serves with it.
srsLagrangeAt
  :: forall f g c
   . ProofFFI f g c
  => CRS g
  -> Int
  -> Int
  -> Array (AffinePoint (F c))
srsLagrangeAt srs log2 i =
  map (\(AffinePoint p) -> AffinePoint { x: F p.x, y: F p.y })
    (srsLagrangeCommitmentChunksAt srs log2 i)

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
        branch b (Vector.index config.stepWidths b) (Vector.index keys b)
    , pins: map (\slots -> map (map fromEnum) (Vector.toUnfoldable slots :: Array (Maybe _)))
        (Vector.toUnfoldable config.prevWrapDomainPins :: Array _)
    , slotWidths: Vector.toUnfoldable slotWidths :: Array Int
    , dummy: map fieldJson
        (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded :: Array WrapField)
    }
  where
  -- branch `b`'s table: its column of each scalar's per-branch bases
  branch b width key =
    { width
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
