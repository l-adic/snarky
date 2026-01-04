module Snarky.Constraint.Kimchi.Wire
  ( KimchiWireRow
  , KimchiRow
  , GateKind(..)
  , emptyKimchiWireState
  , class ToKimchiRows
  , toKimchiRows
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.UnionFind (UnionFindData)
import Data.UnionFind as UnionFind
import Snarky.Circuit.CVar (Variable)
import Snarky.Data.Vector (Vector)

-- Gate kinds for tagging coefficient rows
data GateKind
  = GenericPlonkGate
  | AddCompleteGate
  | PoseidonGate
  | VarBaseMul
  | EndoMul
  | EndoScalar
  | Zero

derive instance Generic GateKind _
instance Show GateKind where
  show x = genericShow x

-- Complete 15-column coefficient row for proof construction
type KimchiRow f =
  { kind :: GateKind
  , variables :: Vector 15 (Maybe Variable)
  , coeffs :: Array f -- 15-column coefficient row  
  }

-- Wire placement state for Kimchi constraint system
type KimchiWireRow f =
  { internalVariables :: Set Variable
  , unionFind :: UnionFindData Variable
  , cachedConstants :: Map f Variable
  }

-- Initial empty wire state
emptyKimchiWireState :: forall f. KimchiWireRow f
emptyKimchiWireState =
  { internalVariables: Set.empty
  , unionFind: UnionFind.emptyUnionFind
  , cachedConstants: Map.empty
  }

class ToKimchiRows f a where
  toKimchiRows :: a -> Array (KimchiRow f)