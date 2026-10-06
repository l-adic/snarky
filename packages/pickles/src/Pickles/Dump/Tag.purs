-- | A tag's independent circuit dump and application reconstruction
-- | sidecar, written by `compileMulti` when dumping is enabled.
module Pickles.Dump.Tag
  ( BranchDump
  , TagFixture
  , ApplicationDump
  , ResolvedDump
  , ImportDump
  , writeTagDump
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.CodeUnits as CodeUnits
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (mkdir', writeTextFile)
import Pickles.CircuitDiffs.Types (ComparableCircuit)
import Pickles.Dump.Constants (KeyExport)
import Pickles.Dump.Environment (EnvironmentDump)
import Pickles.Dump.Shape (ShapeDump, SlotSourceDump(..))
import Pickles.Prove.RuleDump (RuleDumpJson)
import Simple.JSON (writeJSON)

-- | Branch reconstruction inputs and its independently compiled circuit.
type BranchDump =
  { circuit :: ComparableCircuit
  , rule :: RuleDumpJson
  , key :: KeyExport
  , sources :: Array (Maybe ImportDump)
  }

-- | In-memory inputs to the two application fixture files.
type TagFixture =
  { circuit :: ComparableCircuit
  , key :: KeyExport
  , branches :: Array BranchDump
  }

-- | The independent comparison target: gates, wiring and variable identities.
-- | Prover constant caches and diagnostic labels are not comparison inputs.
type CircuitFixture =
  { publicInputSize :: Int
  , gates ::
      Array
        { kind :: String
        , wires :: Array { row :: Int, col :: Int }
        , variables :: Maybe (Array Int)
        , coeffs :: Array String
        }
  }

comparison :: ComparableCircuit -> CircuitFixture
comparison c =
  { publicInputSize: c.publicInputSize
  , gates: c.gates <#> \g ->
      { kind: g.kind, wires: g.wires, variables: g.variables, coeffs: g.coeffs }
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
  require (stepChunks > 0) "the step chunk count is not positive"
  require (Array.length shape.branches == Array.length d.branches)
    "the shape and circuit branch counts differ"
  imports <- foldM collectBranch (Array.replicate (Array.length shape.imports) Nothing)
    (Array.zip shape.branches d.branches)
  resolvedImports <- traverse maybeImport imports
  pure
    { shape
    , rules: map _.rule d.branches
    , resolved:
        { wrapKey: d.key
        , stepKeys: map _.key d.branches
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
    require (Array.length branch.slots == Array.length dumped.sources)
      "the shape and backend slot counts differ"
    foldM collectSlot imports (Array.zip branch.slots dumped.sources)

  collectSlot imports = case _ of
    Tuple SelfSource Nothing -> pure imports
    Tuple (ExternalSource i) (Just entry) -> do
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
  let
    circuits =
      { wrapMain: { circuit: comparison d.circuit }
      , branches: d.branches <#> \b -> { stepMain: { circuit: comparison b.circuit } }
      }
  writeTextFile UTF8 path (writeJSON circuits)
  writeTextFile UTF8 (shapesDir <> "/" <> fileName) (writeJSON application)
