module Pickles.CircuitDiffs.Types
  ( ComparableGate
  , ComparableCircuit
  , CircuitComparison
  , Constants(..)
  , Point
  , Chunked
  , Key
  , WrapBranch
  , StepSlot(..)
  ) where

import Prelude

import Data.Maybe (Maybe)
import Foreign (Foreign, ForeignError(..), fail)
import Simple.JSON (class ReadForeign, class WriteForeign, readImpl, writeImpl)

type ComparableGate =
  { kind :: String
  , wires :: Array { row :: Int, col :: Int }
  , variables :: Maybe (Array Int)
  , coeffs :: Array String
  , context :: Array String
  }

type ComparableCircuit =
  { publicInputSize :: Int
  , gates :: Array ComparableGate
  , cachedConstants :: Array { variable :: Int, varType :: String, value :: String }
  }

-- | A comparison dump: both sides' circuits, the constants the PureScript side was
-- | compiled with, absent for a circuit compiled with none, and a step main's rule
-- | (`encodeRuleDump`).
type CircuitComparison =
  { name :: String
  , status :: String
  , purescript :: ComparableCircuit
  , ocaml :: ComparableCircuit
  , constants :: Maybe Constants
  , rule :: Maybe Foreign
  }

-- | A point as its decimal coordinates, `[x, y]`.
type Point = Array String

-- | A commitment's chunks.
type Chunked = Array Point

-- | A verifier key: its JSON, as the proof cache stores it, and its digest.
type Key = { vk :: String, digest :: String }

-- | A wrap main's branch.
type WrapBranch =
  { width :: Int -- the rule's slot count
  , key :: Key -- its step key
  , lagrange :: Array Chunked -- its table, per public-input cell
  }

-- | A step main's slot.
data StepSlot
  = SelfSlot
      { width :: Int
      , numChunks :: Int
      , domains :: Array Int -- its candidate step domains, log2
      , key :: Key -- the wrap key it verifies against
      , lagrange :: Array Chunked -- its table, per public-input cell
      }
  | ExternalSlot
      { width :: Int
      , numChunks :: Int
      , domains :: Array Int
      , key :: Key
      , lagrange :: Array Chunked
      }
  | SideLoadedSlot
      { width :: Int
      , numChunks :: Int
      , domains :: Array Int
      }

-- | The constants a circuit was compiled with, per kind of circuit.
data Constants
  = Xhat
      { h :: Point -- the blinding base
      , lagrange :: Array Chunked -- per public-input cell
      }
  | XhatBranches
      { h :: Point
      , lagrange :: Array (Array Chunked) -- per branch, per public-input cell
      }
  | WrapMain
      { h :: Point
      , branches :: Array WrapBranch
      , pins :: Array (Array (Maybe Int)) -- per branch, per slot; null when side-loaded
      , slotWidths :: Array Int -- per slot, its challenge-stack height
      , dummy :: Array String -- the padding challenges
      }
  | StepMain
      { h :: Point
      , slots :: Array StepSlot
      }

instance WriteForeign StepSlot where
  writeImpl = case _ of
    SelfSlot r -> writeImpl
      { kind: "self", width: r.width, numChunks: r.numChunks, domains: r.domains, key: r.key, lagrange: r.lagrange }
    ExternalSlot r -> writeImpl
      { kind: "external", width: r.width, numChunks: r.numChunks, domains: r.domains, key: r.key, lagrange: r.lagrange }
    SideLoadedSlot r -> writeImpl
      { kind: "sideLoaded", width: r.width, numChunks: r.numChunks, domains: r.domains }

instance ReadForeign StepSlot where
  readImpl f = do
    { kind } :: { kind :: String } <- readImpl f
    case kind of
      "self" -> SelfSlot <$> readImpl f
      "external" -> ExternalSlot <$> readImpl f
      "sideLoaded" -> SideLoadedSlot <$> readImpl f
      _ -> fail (ForeignError ("unknown slot kind " <> kind))

instance WriteForeign Constants where
  writeImpl = case _ of
    Xhat r -> writeImpl { kind: "xhat", h: r.h, lagrange: r.lagrange }
    XhatBranches r -> writeImpl { kind: "xhatBranches", h: r.h, lagrange: r.lagrange }
    WrapMain r -> writeImpl
      { kind: "wrapMain", h: r.h, branches: r.branches, pins: r.pins, slotWidths: r.slotWidths, dummy: r.dummy }
    StepMain r -> writeImpl { kind: "stepMain", h: r.h, slots: r.slots }

instance ReadForeign Constants where
  readImpl f = do
    { kind } :: { kind :: String } <- readImpl f
    case kind of
      "xhat" -> Xhat <$> readImpl f
      "xhatBranches" -> XhatBranches <$> readImpl f
      "wrapMain" -> WrapMain <$> readImpl f
      "stepMain" -> StepMain <$> readImpl f
      _ -> fail (ForeignError ("unknown constants kind " <> kind))
