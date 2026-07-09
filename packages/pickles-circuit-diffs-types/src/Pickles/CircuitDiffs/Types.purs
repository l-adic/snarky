module Pickles.CircuitDiffs.Types
  ( ComparableGate
  , ComparableCircuit
  , CircuitComparison
  , WitnessExport
  ) where

import Data.Maybe (Maybe)

type ComparableGate =
  { kind :: String
  , wires :: Array { row :: Int, col :: Int }
  , variables :: Maybe (Array Int)
  , coeffs :: Array String
  , context :: Array String
  }

-- | A solved witness for the circuit it hangs off of: the 15 register columns
-- | (column-major) and the public-input values, all field elements as LE-hex strings.
type WitnessExport =
  { witness :: Array (Array String)
  , publicInputs :: Array String
  }

type ComparableCircuit =
  { publicInputSize :: Int
  , gates :: Array ComparableGate
  , cachedConstants :: Array { variable :: Int, varType :: String, value :: String }
  , witness :: Maybe WitnessExport
  }

type CircuitComparison =
  { name :: String
  , status :: String
  , purescript :: ComparableCircuit
  , ocaml :: ComparableCircuit
  }
