module Snarky.Constraint.Kimchi.Wire
  ( KimchiWireRow
  , KimchiRow
  , GateKind(..)
  , emptyKimchiWireState
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.UnionFind (UnionFindData, emptyUnionFind)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Data.Vector (Vector)

-- Gate kinds for tagging coefficient rows
data GateKind
  = GenericPlonkGate
  | AddCompleteGate
  | PoseidonGate

-- Complete 15-column coefficient row for proof construction
type KimchiRow f =
  { kind :: GateKind
  , coeffs :: Vector 15 f -- 15-column coefficient row  
  }

-- Wire placement state for Kimchi constraint system
type KimchiWireRow f =
  { nextRow :: Int -- Current row being filled
  , wireAssignments :: Map Variable (Tuple Int Int) -- Variable -> (row, col) mapping
  , queuedGenericGate :: Maybe (GenericPlonkConstraint f) -- Queued gate for batching
  , emittedRows :: Array (KimchiRow f) -- Complete coefficient rows for proof construction
  , unionFind :: UnionFindData Variable -- Union-find for variable equivalences
  }

-- Initial empty wire state
emptyKimchiWireState :: forall f. KimchiWireRow f
emptyKimchiWireState =
  { nextRow: 0
  , wireAssignments: Map.empty
  , queuedGenericGate: Nothing
  , emittedRows: []
  , unionFind: emptyUnionFind
  }