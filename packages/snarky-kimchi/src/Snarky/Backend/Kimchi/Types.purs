module Snarky.Backend.Kimchi.Types where

import Data.Vector (Vector)
import Snarky.Constraint.Kimchi.Types (GateKind(..))

-- Opaque types for Wire and GateWires from proof-systems
foreign import data Wire :: Type
foreign import data GateWires :: Type

-- Convert PureScript GateKind to string expected by Rust FFI
gateKindToString :: GateKind -> String
gateKindToString = case _ of
  GenericPlonkGate -> "GenericPlonkGate"
  AddCompleteGate -> "AddCompleteGate"
  PoseidonGate -> "PoseidonGate"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoScalar"
  Zero -> "Zero"

-- Create a new wire pointing to the given row and column
foreign import wireNew :: Int -> Int -> Wire

-- Get the row that this wire points to
foreign import wireGetRow :: Wire -> Int

-- Get the column that this wire points to  
foreign import wireGetCol :: Wire -> Int

-- Create gate wires from exactly 7 wires
foreign import gateWiresNewFromWires :: Vector 7 Wire -> GateWires

-- Get the wire at the specified column (0-6)
foreign import gateWiresGetWire :: GateWires -> Int -> Wire

foreign import data CRS :: Type -> Type
foreign import data ConstraintSystem :: Type -> Type
foreign import data Gate :: Type -> Type
foreign import data ProverIndex :: Type -> Type -> Type
foreign import data VerifierIndex :: Type -> Type -> Type