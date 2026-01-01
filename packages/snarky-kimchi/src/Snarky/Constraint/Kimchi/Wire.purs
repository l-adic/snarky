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
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Snarky.Circuit.CVar (Variable)
import Snarky.Data.Vector (Vector)

-- Gate kinds for tagging coefficient rows
data GateKind
  = GenericPlonkGate
  | AddCompleteGate
  | PoseidonGate
  | VarBaseMul
  | EndoScale
  | Zero

derive instance Generic GateKind _
instance Show GateKind where
  show x = genericShow x

-- Complete 15-column coefficient row for proof construction
type KimchiRow f =
  { kind :: GateKind
  , variables :: Vector 15 (Maybe Variable)
  , coeffs :: Vector 15 f -- 15-column coefficient row  
  }

-- Wire placement state for Kimchi constraint system
type KimchiWireRow :: forall k. k -> Type
type KimchiWireRow f =
  { internalVariables :: Set Variable
  }

-- Initial empty wire state
emptyKimchiWireState :: forall f. KimchiWireRow f
emptyKimchiWireState =
  { internalVariables: Set.empty
  }

class ToKimchiRows f a where
  toKimchiRows :: a -> Array (KimchiRow f)