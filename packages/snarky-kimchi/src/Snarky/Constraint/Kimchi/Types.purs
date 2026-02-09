module Snarky.Constraint.Kimchi.Types
  ( GenericPlonkConstraint
  , AuxState(..)
  , initialAuxState
  , GateKind(..)
  , KimchiRow
  , KimchiWireRow
  , emptyKimchiWireState
  , class ToKimchiRows
  , toKimchiRows
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.UnionFind (UnionFindData)
import Data.UnionFind as UnionFind
import Data.Vector (Vector)
import Snarky.Circuit.DSL (Variable)

type GenericPlonkConstraint f =
  { cl :: f -- Left coefficient
  , vl :: Maybe Variable -- Left variable
  , cr :: f -- Right coefficient  
  , vr :: Maybe Variable -- Right variable
  , co :: f -- Output coefficient
  , vo :: Maybe Variable -- Output variable
  , m :: f -- Multiplication coefficient  
  , c :: f -- Constant term
  }

newtype AuxState f = AuxState
  { wireState :: KimchiWireRow f
  , queuedGenericGate :: Maybe (GenericPlonkConstraint f)
  }

derive instance Newtype (AuxState f) _

initialAuxState :: forall f. AuxState f
initialAuxState = AuxState
  { wireState: emptyKimchiWireState
  , queuedGenericGate: Nothing
  }

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