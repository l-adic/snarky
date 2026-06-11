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
import Data.UnionFind.Mutable (MutableUF)
import Data.UnionFind.Mutable as MutableUF
import Data.Vector (Vector)
import Effect (Effect)
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

initialAuxState :: forall f. Effect (AuxState f)
initialAuxState = do
  uf <- MutableUF.fresh
  pure $ AuxState
    { wireState: emptyKimchiWireState uf
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

derive instance Eq GateKind
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
  , unionFind :: MutableUF
  , cachedConstants :: Map f Variable
  }

-- Initial empty wire state
emptyKimchiWireState :: forall f. MutableUF -> KimchiWireRow f
emptyKimchiWireState uf =
  { internalVariables: Set.empty
  , unionFind: uf
  , cachedConstants: Map.empty
  }

class ToKimchiRows f a where
  toKimchiRows :: a -> Array (KimchiRow f)
