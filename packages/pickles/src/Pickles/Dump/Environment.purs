-- | Shared protocol inputs for application reconstruction. SRS references
-- | name the curve and truncation; the reader supplies the shared files.
module Pickles.Dump.Environment
  ( EnvironmentDump
  , SrsReference
  , ChallengesDump
  , environmentDump
  ) where

import Prelude

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Reflectable (reflectType)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.Types (Point)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Step.Dummy (baseCaseDummies, mkDummyPerProofUnfinalized)
import Pickles.Types (AllocEvals, MaxProofsVerified, StepIPARounds, WrapIPARounds)
import Snarky.Backend.Kimchi.Proof (srsBlindingGenerator)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F, valueToFields)
import Snarky.Circuit.DSL.SizedF (toField)
import Snarky.Curves.Class (class PrimeField, toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The blinding point is a consistency check, not an SRS identity.
type SrsReference = { curve :: String, rounds :: Int, h :: Point }

type ChallengesDump = { raw :: Array String, expanded :: Array String }

type EnvironmentDump =
  { srs :: { wrap :: SrsReference, step :: SrsReference }
  , padding ::
      { wrapChallenges :: ChallengesDump
      , stepChallenges :: ChallengesDump
      , unfinalized :: Array { predecessors :: Int, fields :: Array String }
      , wrapEvals :: Array String
      , wrapDomain :: Int -- ^ The `ProofsVerified` index, not a domain log2.
      }
  }

-- | Padding at every supported predecessor count, independent of the tag.
-- | Accumulator commitments are derived from these challenges and the SRS.
environmentDump
  :: { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG }
  -> ProofsVerified
  -> AllocEvals (F WrapField)
  -> EnvironmentDump
environmentDump srs wrapDomain wrapEvals =
  { srs:
      { wrap:
          { curve: "pallas"
          , rounds: reflectType (Proxy @WrapIPARounds)
          , h: point (srsBlindingGenerator srs.pallasSrs)
          }
      , step:
          { curve: "vesta"
          , rounds: reflectType (Proxy @StepIPARounds)
          , h: point (srsBlindingGenerator srs.vestaSrs)
          }
      }
  , padding:
      { wrapChallenges:
          { raw: map (field <<< toField) (Vector.toUnfoldable dummyIpaChallenges.wrapRaw)
          , expanded: map field (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded)
          }
      , stepChallenges:
          { raw: map (field <<< toField) (Vector.toUnfoldable dummyIpaChallenges.stepRaw)
          , expanded: map field (Vector.toUnfoldable dummyIpaChallenges.stepExpanded)
          }
      , unfinalized: Array.range 0 (reflectType (Proxy @MaxProofsVerified)) <#> \predecessors ->
          { predecessors
          , fields: map field $ valueToFields @StepField $ mkDummyPerProofUnfinalized $
              baseCaseDummies { maxProofsVerified: predecessors }
          }
      , wrapEvals: map field (valueToFields @WrapField wrapEvals)
      , wrapDomain: fromEnum wrapDomain
      }
  }

field :: forall f. PrimeField f => f -> String
field = BigInt.toString <<< toBigInt

point :: forall f. PrimeField f => AffinePoint f -> Point
point (AffinePoint { x, y }) = [ field x, field y ]
