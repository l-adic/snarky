module Pickles.CircuitDiffs.Circuit
  ( parseOcamlFixtures
  , parseCircuitJson
  , parseCachedConstants
  , parseGateLabels
  , module ReExports
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either, note)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Vector as Vector
import Foreign (ForeignError(..), MultipleErrors)
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.Types (CircuitComparison, ComparableCircuit, ComparableGate) as ReExports
import Pickles.Dump.Circuit (CachedConstant, Circuit, GateData)
import Simple.JSON (class ReadForeign, readJSON)
import Snarky.Constraint.Kimchi.Types (GateKind(..))
import Snarky.Curves.Class (class PrimeField, class SerdeHex, fromBigInt, fromHexLe)

--------------------------------------------------------------------------------
-- From OCaml fixture files

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

parseVariable :: String -> Maybe { variable :: Int, varType :: String }
parseVariable s = do
  inner <- String.stripPrefix (String.Pattern "(") s >>= String.stripSuffix (String.Pattern ")")
  let parts = String.split (String.Pattern " ") inner
  varType <- Array.head parts
  numStr <- Array.last parts
  variable <- Int.fromString numStr
  pure { variable, varType: String.toLower varType }

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
      , variables: Vector.replicate Nothing
      , coeffs: map fromHexLe g.coeffs
      , context: []
      }

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
    { variable, varType } <- note (pure $ ForeignError $ "Cannot parse variable: " <> var) (parseVariable var)
    f <- note (pure $ ForeignError $ "Cannot parse decimal field value: " <> value)
      (fromBigInt <$> BigInt.fromString value)
    pure { variable, varType, value: f }

parseGateLabels :: String -> Either MultipleErrors (Array (Array String))
parseGateLabels input = do
  raw :: Array GateLabelRaw <- parseJsonl input
  pure $ map _.context raw

parseOcamlFixtures
  :: forall f
   . SerdeHex f
  => PrimeField f
  => { circuit :: String
     , cachedConstants :: String
     , gateLabels :: String
     }
  -> Either MultipleErrors (Circuit f)
parseOcamlFixtures files = do
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
