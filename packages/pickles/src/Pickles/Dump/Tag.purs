-- | A tag's independent circuit dump and application reconstruction
-- | sidecar, written by `compileMulti` when dumping is enabled.
module Pickles.Dump.Tag
  ( CircuitDump
  , BranchDump
  , TagFixture
  , ApplicationDump
  , ResolvedDump
  , ImportDump
  , WrapPadding
  , wrapPadding
  , writeTagDump
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Enum (fromEnum)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.CodeUnits as CodeUnits
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (mkdir', writeTextFile)
import Pickles.CircuitDiffs.Types (ComparableCircuit, Constants(..), Point, StepSlot(..))
import Pickles.Dump.Constants (KeyExport)
import Pickles.Dump.Environment (EnvironmentDump)
import Pickles.Dump.Shape (ShapeDump, SlotSourceDump(..))
import Pickles.Field (WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Prove.RuleDump (RuleDumpJson)
import Pickles.Types (AllocEvals)
import Simple.JSON (writeJSON)
import Snarky.Circuit.DSL (F(..), valueToFields)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))

-- | A circuit as dumped: its constraint system and the constants it
-- | bakes in, with the fields in `r`.
type CircuitDump r =
  { circuit :: ComparableCircuit
  , constants :: Constants
  | r
  }

-- | A branch: its step circuit and its rule.
type BranchDump =
  { stepMain :: CircuitDump ()
  , rule :: RuleDumpJson
  }

-- | What the wrap prover allocates for a slot its rule lacks: the step
-- | proof's accumulator, the evaluations' cells and the wrap domain's
-- | index.
type WrapPadding = { stepAcc :: Point, evals :: Array String, domain :: Int }

-- | The padding values as the dump records them.
wrapPadding
  :: { stepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
     , evals :: AllocEvals (F WrapField)
     , domain :: ProofsVerified
     }
  -> WrapPadding
wrapPadding p =
  { stepAcc: case p.stepAcc of
      WeierstrassAffinePoint { x: F x, y: F y } -> [ field x, field y ]
  , evals: map field (valueToFields @WrapField p.evals)
  , domain: fromEnum p.domain
  }
  where
  field :: WrapField -> String
  field = BigInt.toString <<< toBigInt

-- | A tag's independently compiled circuits and their comparison inputs.
type TagFixture =
  { wrapMain :: CircuitDump (key :: KeyExport, padding :: WrapPadding)
  , branches :: Array BranchDump
  }

-- | Backend data for an import, in the shape's import-index order.
type ImportDump =
  { wrapKey :: KeyExport
  , stepChunks :: Int
  , stepDomains :: Array Int
  }

type ResolvedDump =
  { wrapKey :: KeyExport
  , stepKeys :: Array KeyExport
  , stepChunks :: Int
  , imports :: Array ImportDump
  }

-- | One application's reconstruction inputs, without gates or witnesses.
-- | Lagrange tables are derived from the shared SRS and key domains.
type ApplicationDump =
  { shape :: ShapeDump
  , rules :: Array RuleDumpJson
  , resolved :: ResolvedDump
  , environment :: EnvironmentDump
  }

-- | Assemble the sidecar from shape and backend metadata. No compiled
-- | gate rows or witness assignments are read.
applicationDump
  :: ShapeDump
  -> Int
  -> EnvironmentDump
  -> TagFixture
  -> Either String ApplicationDump
applicationDump shape stepChunks environment d = do
  wrap <- case d.wrapMain.constants of
    WrapMain w -> Right w
    _ -> Left "application dump: expected wrap-main constants"
  require (stepChunks > 0) "the step chunk count is not positive"
  require (Array.length shape.branches == Array.length d.branches)
    "the shape and circuit branch counts differ"
  require (Array.length wrap.branches == Array.length d.branches)
    "the wrap and step branch counts differ"
  imports <- foldM collectBranch (Array.replicate (Array.length shape.imports) Nothing)
    (Array.zip shape.branches d.branches)
  resolvedImports <- traverse maybeImport imports
  pure
    { shape
    , rules: map _.rule d.branches
    , resolved:
        { wrapKey: d.wrapMain.key
        , stepKeys: map _.key wrap.branches
        , stepChunks
        , imports: resolvedImports
        }
    , environment
    }
  where
  maybeImport = case _ of
    Just entry -> Right entry
    Nothing -> Left "application dump: an import has no backend metadata"

  collectBranch imports (Tuple branch dumped) = do
    step <- case dumped.stepMain.constants of
      StepMain s -> Right s
      _ -> Left "application dump: expected step-main constants"
    require (Array.length branch.slots == Array.length step.slots)
      "the shape and backend slot counts differ"
    foldM collectSlot imports (Array.zip branch.slots step.slots)

  collectSlot imports = case _ of
    Tuple SelfSource (SelfSlot s) -> do
      require (writeJSON s.key == writeJSON d.wrapMain.key)
        "a Self slot has a different wrap key"
      pure imports
    Tuple (ExternalSource i) (ExternalSlot s) -> do
      let entry = { wrapKey: s.key, stepChunks: s.numChunks, stepDomains: s.domains }
      case Array.index imports i of
        Nothing -> Left "application dump: an import index is out of bounds"
        Just (Just previous) -> do
          require (writeJSON entry == writeJSON previous)
            "an imported source has inconsistent backend metadata"
          pure imports
        Just Nothing -> case Array.updateAt i (Just entry) imports of
          Just updated -> pure updated
          Nothing -> Left "application dump: an import index is out of bounds"
    Tuple (SideLoadedSource _) _ ->
      Left "application dump: side-loaded rules are not replayable"
    _ -> Left "application dump: the shape and backend slot kinds differ"

require :: Boolean -> String -> Either String Unit
require true _ = Right unit
require false message = Left ("application dump: " <> message)

-- | Write the circuit fixture and one reconstruction sidecar at
-- | `shapes/<tag>.json`. Both are serialized from typed records.
writeTagDump :: String -> ShapeDump -> Int -> EnvironmentDump -> TagFixture -> Effect Unit
writeTagDump path shape stepChunks environment d = do
  application <- either throw pure (applicationDump shape stepChunks environment d)
  let
    { dir, fileName } = case lastIndexOf (Pattern "/") path of
      Just i -> { dir: take i path, fileName: CodeUnits.drop (i + 1) path }
      Nothing -> { dir: ".", fileName: path }
    shapesDir = dir <> "/shapes"
  mkdir' dir { recursive: true, mode: permsAll }
  mkdir' shapesDir { recursive: true, mode: permsAll }
  writeTextFile UTF8 path (writeJSON d)
  writeTextFile UTF8 (shapesDir <> "/" <> fileName) (writeJSON application)
