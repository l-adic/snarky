-- | The static application description written beside a tag's circuits.
-- | It records statement field layouts and the branch-local predecessor
-- | sources, without depending on the circuits or their backend constants.
module Pickles.Dump.Shape
  ( FieldLayoutDump
  , ImportedLayoutDump
  , SlotSourceDump(..)
  , BranchShapeDump
  , ShapeDump
  , SlotSourceSeed(..)
  , SlotSeed
  , BranchShapeSeed
  , assembleShape
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Foreign (ForeignError(..), fail)
import Simple.JSON (class ReadForeign, class WriteForeign, readImpl, writeImpl)

type FieldLayoutDump = { inputFields :: Int, outputFields :: Int }

type ImportedLayoutDump = { statement :: FieldLayoutDump, width :: Int }

-- | An External index addresses `ShapeDump.imports`. A side-loaded slot
-- | carries its own declared interface because it has no compiled import.
data SlotSourceDump
  = SelfSource
  | ExternalSource Int
  | SideLoadedSource ImportedLayoutDump

derive instance Eq SlotSourceDump

instance WriteForeign SlotSourceDump where
  writeImpl = case _ of
    SelfSource -> writeImpl { kind: "self" }
    ExternalSource importIndex -> writeImpl { kind: "external", importIndex }
    SideLoadedSource layout -> writeImpl
      { kind: "sideLoaded", statement: layout.statement, width: layout.width }

instance ReadForeign SlotSourceDump where
  readImpl f = do
    { kind } :: { kind :: String } <- readImpl f
    case kind of
      "self" -> pure SelfSource
      "external" -> do
        { importIndex } :: { importIndex :: Int } <- readImpl f
        pure (ExternalSource importIndex)
      "sideLoaded" -> SideLoadedSource <$> readImpl f
      _ -> fail (ForeignError ("unknown slot source kind " <> kind))

type BranchShapeDump = { slots :: Array SlotSourceDump }

type ShapeDump =
  { statement :: FieldLayoutDump
  , imports :: Array ImportedLayoutDump
  , branches :: Array BranchShapeDump
  }

-- | Only an imported source's complete key identity and width are needed
-- | to register it. The key is internal and never appears in `ShapeDump`.
data SlotSourceSeed
  = SelfSeed
  | ExternalSeed { key :: String, statement :: FieldLayoutDump, width :: Int }
  | SideLoadedSeed

-- | Captured from one rule's slot specification and its supplied key
-- | sources, before any circuit is built.
type SlotSeed =
  { statement :: FieldLayoutDump
  , width :: Int
  , source :: SlotSourceSeed
  }

type BranchShapeSeed =
  { statement :: FieldLayoutDump
  , slots :: Array SlotSeed
  }

-- | The complete key is retained only during import numbering. Repeated
-- | uses of one compiled source receive the same first-use index.
type RegisteredImport =
  { key :: String
  , layout :: ImportedLayoutDump
  }

type AssemblyState =
  { imports :: Array RegisteredImport
  , branches :: Array BranchShapeDump
  }

check :: Boolean -> String -> Either String Unit
check true _ = pure unit
check false message = Left message

fieldCount :: FieldLayoutDump -> Int
fieldCount layout = layout.inputFields + layout.outputFields

-- | Resolve branch-local sources to a deterministic import registry. The
-- | same complete wrap key must always carry the same source layout and
-- | declared width. A slot's own encoding need only have the source's total
-- | number of fields; its input/output split may differ.
assembleShape :: Array BranchShapeSeed -> Either String ShapeDump
assembleShape seeds = do
  first <- case Array.head seeds of
    Just branch -> pure branch
    Nothing -> Left "an application must have at least one branch"
  let
    statement = first.statement
    width = Array.foldl max 0 (map (Array.length <<< _.slots) seeds)
    indexed = Array.mapWithIndex (\index branch -> { index, branch }) seeds
  state <- foldM (assembleBranch statement width)
    { imports: [], branches: [] }
    indexed
  pure
    { statement
    , imports: map _.layout state.imports
    , branches: state.branches
    }

assembleBranch
  :: FieldLayoutDump
  -> Int
  -> AssemblyState
  -> { index :: Int, branch :: BranchShapeSeed }
  -> Either String AssemblyState
assembleBranch statement width state { index, branch } = do
  check (branch.statement == statement)
    ("branch " <> show index <> " has a different application statement layout")
  let indexed = Array.mapWithIndex (\slot seed -> { slot, seed }) branch.slots
  result <- foldM (assembleSlot statement width index)
    { imports: state.imports, slots: [] }
    indexed
  pure
    { imports: result.imports
    , branches: Array.snoc state.branches { slots: result.slots }
    }

assembleSlot
  :: FieldLayoutDump
  -> Int
  -> Int
  -> { imports :: Array RegisteredImport, slots :: Array SlotSourceDump }
  -> { slot :: Int, seed :: SlotSeed }
  -> Either String { imports :: Array RegisteredImport, slots :: Array SlotSourceDump }
assembleSlot statement width branch { imports, slots } { slot, seed } = do
  let
    label = "branch " <> show branch <> " slot " <> show slot
    layout = { statement: seed.statement, width: seed.width }
    append source nextImports =
      { imports: nextImports, slots: Array.snoc slots source }
  check (seed.width >= 0) (label <> " has a negative width")
  case seed.source of
    SideLoadedSeed -> pure (append (SideLoadedSource layout) imports)
    SelfSeed -> do
      check (fieldCount seed.statement == fieldCount statement)
        (label <> " has a Self statement field count different from its application")
      check (seed.width == width)
        (label <> " has a Self width different from its application")
      pure (append SelfSource imports)
    ExternalSeed source -> do
      let sourceLayout = { statement: source.statement, width: source.width }
      check (fieldCount seed.statement == fieldCount source.statement)
        (label <> " has a statement field count different from its imported application")
      check (seed.width == source.width)
        (label <> " has a width different from its imported application")
      case Array.findIndex (\entry -> entry.key == source.key) imports of
        Nothing -> pure
          ( append (ExternalSource (Array.length imports))
              (Array.snoc imports { key: source.key, layout: sourceLayout })
          )
        Just importIndex -> do
          entry <- case Array.index imports importIndex of
            Just found -> pure found
            Nothing -> Left (label <> " has an invalid import index")
          check (entry.layout == sourceLayout)
            (label <> " reuses an imported key with a different source layout or width")
          pure (append (ExternalSource importIndex) imports)
