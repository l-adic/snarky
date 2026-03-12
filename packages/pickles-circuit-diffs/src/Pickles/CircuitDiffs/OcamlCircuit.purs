module Pickles.CircuitDiffs.OcamlCircuit
  ( OcamlCircuit
  , GateData
  , CachedConstant
  , parseCircuitJson
  , parseCachedConstants
  , parseGateLabels
  , parseOcamlCircuit
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either, note)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse)
import Foreign (ForeignError(..), MultipleErrors)
import JS.BigInt as BigInt
import Simple.JSON (class ReadForeign, readJSON)
import Snarky.Constraint.Kimchi.Types (GateKind(..))
import Snarky.Curves.Class (class PrimeField, class SerdeHex, fromBigInt, fromHexLe)

--------------------------------------------------------------------------------
-- Target types

type GateData f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array f
  , context :: Array String
  }

type CachedConstant f =
  { variable :: Int
  , value :: f
  }

type OcamlCircuit f =
  { publicInputSize :: Int
  , gates :: Array (GateData f)
  , cachedConstants :: Array (CachedConstant f)
  }

--------------------------------------------------------------------------------
-- Raw JSON types (field names match JSON keys for simple-json auto-derivation)

type CircuitJsonRaw =
  { public_input_size :: Int
  , gates :: Array GateRaw
  }

type GateRaw =
  { typ :: String
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array String
  }

type CachedConstantRaw =
  { var :: String
  , value :: String
  }

type GateLabelRaw =
  { row :: Int
  , context :: Array String
  }

--------------------------------------------------------------------------------
-- Gate kind mapping (OCaml/Rust JSON string → GateKind)

gateKindFromString :: String -> Maybe GateKind
gateKindFromString = case _ of
  "Zero" -> Just Zero
  "Generic" -> Just GenericPlonkGate
  "Poseidon" -> Just PoseidonGate
  "CompleteAdd" -> Just AddCompleteGate
  "VarBaseMul" -> Just VarBaseMul
  "EndoMul" -> Just EndoMul
  "EndoMulScalar" -> Just EndoScalar
  _ -> Nothing

--------------------------------------------------------------------------------
-- Variable string parsing: "(Internal 5712)" or "(External 0)" → Int

parseVariable :: String -> Maybe Int
parseVariable s = do
  inner <- String.stripPrefix (String.Pattern "(") s >>= String.stripSuffix (String.Pattern ")")
  let parts = String.split (String.Pattern " ") inner
  numStr <- Array.last parts
  Int.fromString numStr

--------------------------------------------------------------------------------
-- Parsers

-- | Parse the main circuit .json file. Coefficients are hex LE encoded.
-- | Gates get empty context; use parseOcamlCircuit to merge gate labels.
parseCircuitJson
  :: forall f
   . SerdeHex f
  => String
  -> Either MultipleErrors { publicInputSize :: Int, gates :: Array (GateData f) }
parseCircuitJson json = do
  raw :: CircuitJsonRaw <- readJSON json
  gates <- traverse convertGate raw.gates
  pure { publicInputSize: raw.public_input_size, gates }
  where
  convertGate :: GateRaw -> Either MultipleErrors (GateData f)
  convertGate g = do
    kind <- note (pure $ ForeignError $ "Unknown gate type: " <> g.typ) (gateKindFromString g.typ)
    pure
      { kind
      , wires: g.wires
      , coeffs: map fromHexLe g.coeffs
      , context: []
      }

-- | Parse the _cached_constants.json file. Values are decimal encoded.
parseCachedConstants
  :: forall f
   . PrimeField f
  => String
  -> Either MultipleErrors (Array (CachedConstant f))
parseCachedConstants json = do
  raw :: Array CachedConstantRaw <- readJSON json
  traverse convertConstant raw
  where
  convertConstant :: CachedConstantRaw -> Either MultipleErrors (CachedConstant f)
  convertConstant { var, value } = do
    variable <- note (pure $ ForeignError $ "Cannot parse variable: " <> var) (parseVariable var)
    f <- note (pure $ ForeignError $ "Cannot parse decimal field value: " <> value)
      (fromBigInt <$> BigInt.fromString value)
    pure { variable, value: f }

-- | Parse the _gate_labels.jsonl file (one JSON object per line).
parseGateLabels :: String -> Either MultipleErrors (Array (Array String))
parseGateLabels input = do
  raw :: Array GateLabelRaw <- parseJsonl input
  pure $ map _.context raw

-- | Parse all files into a unified OcamlCircuit.
-- | Gate labels are merged into gates by row index.
parseOcamlCircuit
  :: forall f
   . SerdeHex f
  => PrimeField f
  => { circuit :: String
     , cachedConstants :: String
     , gateLabels :: String
     }
  -> Either MultipleErrors (OcamlCircuit f)
parseOcamlCircuit files = do
  { publicInputSize, gates } <- parseCircuitJson files.circuit
  cachedConstants <- parseCachedConstants files.cachedConstants
  contexts <- parseGateLabels files.gateLabels
  let
    gatesWithContext = Array.zipWith
      (\gate ctx -> gate { context = ctx })
      gates
      (contexts <> Array.replicate (Array.length gates) [])
  pure { publicInputSize, gates: gatesWithContext, cachedConstants }

--------------------------------------------------------------------------------
-- JSONL helper

parseJsonl :: forall a. ReadForeign a => String -> Either MultipleErrors (Array a)
parseJsonl input =
  let
    lines = Array.filter (not <<< String.null) $ String.split (String.Pattern "\n") input
  in
    traverse readJSON lines
