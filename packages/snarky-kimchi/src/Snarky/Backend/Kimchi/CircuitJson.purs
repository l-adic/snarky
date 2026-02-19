module Snarky.Backend.Kimchi.CircuitJson
  ( CircuitData
  , CircuitGateData
  , readCircuitJson
  , circuitToJson
  , gateKindFromRust
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Either (Either, note)
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Traversable (traverse)
import Foreign (ForeignError(..), MultipleErrors)
import Simple.JSON (readJSON)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makeGateData)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, gatesToJson)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), toKimchiRows)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, fromHexLe)

-- | Typed circuit data with parsed field elements and gate kinds.
type CircuitData f =
  { publicInputSize :: Int
  , gates :: Array (CircuitGateData f)
  }

-- | A single gate with parsed type, wires, and coefficients.
type CircuitGateData f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array f
  }

-- Raw JSON shape (field names match JSON keys exactly for simple-json auto-derivation)
type CircuitJsonRaw =
  { public_input_size :: Int
  , gates :: Array CircuitGateRaw
  }

type CircuitGateRaw =
  { typ :: String
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array String
  }

-- | Convert Rust GateType enum name to PureScript GateKind.
gateKindFromRust :: String -> Maybe GateKind
gateKindFromRust = case _ of
  "Zero" -> Just Zero
  "Generic" -> Just GenericPlonkGate
  "Poseidon" -> Just PoseidonGate
  "CompleteAdd" -> Just AddCompleteGate
  "VarBaseMul" -> Just VarBaseMul
  "EndoMul" -> Just EndoMul
  "EndoMulScalar" -> Just EndoScalar
  _ -> Nothing

-- | Parse a circuit JSON string into structured data with typed field elements.
readCircuitJson :: forall f. SerdeHex f => String -> Either MultipleErrors (CircuitData f)
readCircuitJson json = do
  raw :: CircuitJsonRaw <- readJSON json
  gates <- traverse convertGate raw.gates
  pure { publicInputSize: raw.public_input_size, gates }
  where
  convertGate :: CircuitGateRaw -> Either MultipleErrors (CircuitGateData f)
  convertGate g = do
    kind <- note (pure $ ForeignError $ "Unknown gate type: " <> g.typ) (gateKindFromRust g.typ)
    pure
      { kind
      , wires: g.wires
      , coeffs: map fromHexLe g.coeffs
      }

-- | Serialize a compiled circuit builder state to JSON (no ConstraintSystem padding).
-- | This matches the OCaml `to_json` behavior which serializes the gate vector directly.
circuitToJson
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> String
circuitToJson s =
  let
    { gates, publicInputSize } = makeGateData @f
      { constraints: concatMap toKimchiRows s.constraints
      , publicInputs: s.publicInputs
      , unionFind: (un AuxState s.aux).wireState.unionFind
      }
  in
    gatesToJson gates publicInputSize
