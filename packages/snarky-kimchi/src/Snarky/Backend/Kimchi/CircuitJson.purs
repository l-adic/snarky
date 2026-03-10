module Snarky.Backend.Kimchi.CircuitJson
  ( CircuitData
  , CircuitGateData
  , readCircuitJson
  , readCachedConstantsJson
  , circuitToJson
  , extractCachedConstants
  , gateKindFromRust
  , GateDiff
  , diffCircuits
  , formatGate
  , formatCircuit
  , rowContexts
  ) where

import Prelude

import Data.Array (concatMap, mapWithIndex, replicate)
import Data.Array as Array
import Data.Either (Either, note)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Foreign (ForeignError(..), MultipleErrors)
import JS.BigInt as BigInt
import Simple.JSON (readJSON)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makeGateData)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, gatesToJson)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, fromBigInt, fromHexLe)

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
      { constraints: concatMap (toKimchiRows <<< _.constraint) s.constraints
      , publicInputs: s.publicInputs
      , unionFind: (un AuxState s.aux).wireState.unionFind
      }
  in
    gatesToJson gates publicInputSize

--------------------------------------------------------------------------------
-- | Cached constants

-- | Raw JSON shape for cached constants fixture
type CachedConstantRaw =
  { var :: String
  , value :: String
  }

-- | Parse OCaml cached constants fixture JSON.
-- | Returns the set of constant values (ignoring variable IDs).
readCachedConstantsJson
  :: forall f
   . Ord f
  => PrimeField f
  => String
  -> Either MultipleErrors (Array (Tuple String f))
readCachedConstantsJson json = do
  raw :: Array CachedConstantRaw <- readJSON json
  let
    values = Array.mapMaybe
      ( \{ var, value } -> do
          f <- fromBigInt <$> BigInt.fromString value
          pure $ Tuple var f
      )
      raw
  pure $ Array.sortWith fst values

-- | Extract the set of cached constant values from a compiled PS circuit.
extractCachedConstants
  :: forall f
   . Ord f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Array (Tuple String f)
extractCachedConstants s =
  let
    AuxState aux = s.aux
    cs = (\(Tuple x y) -> Tuple (show y) x) <$> Map.toUnfoldableUnordered aux.wireState.cachedConstants
  in
    Array.sortWith fst cs

--------------------------------------------------------------------------------
-- | Comparison utilities

-- | A gate that differs between two circuits.
type GateDiff f =
  { index :: Int
  , ocaml :: CircuitGateData f
  , ps :: CircuitGateData f
  }

-- | Find gates that differ between two circuits.
diffCircuits :: forall f. Eq f => CircuitData f -> CircuitData f -> Array (GateDiff f)
diffCircuits ocaml ps =
  Array.catMaybes $ mapWithIndex
    ( \i (Tuple o p) ->
        if o == p then Nothing
        else Just { index: i, ocaml: o, ps: p }
    )
    (Array.zip ocaml.gates ps.gates)

-- | Format a single gate for display.
formatGate :: forall f. Show f => Int -> CircuitGateData f -> String
formatGate i g = "  [" <> show i <> "] " <> show g.kind
  <> " wires="
  <> show g.wires
  <> " coeffs="
  <> show g.coeffs

-- | Format an entire circuit for display.
formatCircuit :: forall f. Show f => String -> CircuitData f -> Array String
formatCircuit label c =
  [ label <> " (pi=" <> show c.publicInputSize <> ", gates=" <> show (Array.length c.gates) <> "):" ]
    <> mapWithIndex formatGate c.gates

-- | Extract per-row context labels from a compiled circuit.
-- | Returns one context per row, in gate order (public input rows get empty context).
rowContexts
  :: forall f
   . PrimeField f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Array (Array String)
rowContexts s =
  let
    piContexts = replicate (Array.length s.publicInputs) []
    gateContexts = concatMap
      (\lc -> replicate (Array.length (toKimchiRows lc.constraint :: Array (KimchiRow f))) lc.context)
      s.constraints
  in
    piContexts <> gateContexts
