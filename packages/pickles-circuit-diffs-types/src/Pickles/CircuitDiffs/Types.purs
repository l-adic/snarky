module Pickles.CircuitDiffs.Types
  ( ComparableGate
  , ComparableCircuit
  ) where

type ComparableGate =
  { kind :: String
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array String
  , context :: Array String
  }

type ComparableCircuit =
  { publicInputSize :: Int
  , gates :: Array ComparableGate
  , cachedConstants :: Array String
  }
