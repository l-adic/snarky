module Snarky.Backend.Kimchi.Circuit where

import Prelude

import Snarky.Data.Vector (Vector)

-- ============================================================================
-- FOREIGN TYPES
-- ============================================================================

-- Opaque types for Wire and GateWires from proof-systems
foreign import data Wire :: Type
foreign import data GateWires :: Type

-- ============================================================================
-- WIRE OPERATIONS
-- ============================================================================

-- Create a new wire pointing to the given row and column
foreign import wireNew :: Int -> Int -> Wire

-- Get the row that this wire points to
foreign import wireGetRow :: Wire -> Int

-- Get the column that this wire points to  
foreign import wireGetCol :: Wire -> Int

-- ============================================================================
-- GATE WIRES OPERATIONS (7-element wire array)
-- ============================================================================

-- Create gate wires from exactly 7 wires
foreign import gateWiresNewFromWires :: Vector 7 Wire -> GateWires

-- Get the wire at the specified column (0-6)
foreign import gateWiresGetWire :: GateWires -> Int -> Wire

