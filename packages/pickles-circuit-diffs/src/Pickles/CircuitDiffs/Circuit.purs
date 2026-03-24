module Pickles.CircuitDiffs.Circuit
  ( Circuit
  , GateData
  , CachedConstant
  , comparable
  , fromCompiledCircuit
  , parseOcamlFixtures
  , parseCircuitJson
  , parseCachedConstants
  , parseGateLabels
  , module ReExports
  ) where

import Prelude

import Data.Array (concatMap, replicate)
import Data.Array as Array
import Data.Either (Either, note)
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Foreign (ForeignError(..), MultipleErrors)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.Types (CircuitComparison, ComparableCircuit, ComparableGate) as ReExports
import Pickles.CircuitDiffs.Types (ComparableCircuit)
import Simple.JSON (class ReadForeign, readJSON)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makeGateData)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, circuitGateGetWires)
import Snarky.Backend.Kimchi.Types (gateWiresGetWire, wireGetCol, wireGetRow)
import Snarky.Circuit.CVar (getVariable)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, fromBigInt, fromHexLe, modulus, toBigInt)

gateKindToString :: GateKind -> String
gateKindToString = case _ of
  Zero -> "Zero"
  GenericPlonkGate -> "Generic"
  PoseidonGate -> "Poseidon"
  AddCompleteGate -> "CompleteAdd"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoMulScalar"

-- | Convert a field element to a signed decimal string.
-- | Values > p/2 are shown as negative (e.g. p-1 becomes "-1").
toSignedDecimal :: forall f. PrimeField f => f -> String
toSignedDecimal x =
  let
    n = toBigInt x
    p = modulus @f
    half = p / BigInt.fromInt 2
  in
    if n > half then "-" <> BigInt.toString (p - n)
    else BigInt.toString n

-- | Convert variable vector to Maybe array.
-- | Returns Nothing if all variables are unset (e.g. OCaml-parsed gates).
varsToMaybe :: Vector 15 (Maybe Int) -> Maybe (Array Int)
varsToMaybe v =
  let
    arr = Vector.toUnfoldable v :: Array (Maybe Int)
    toInt = case _ of
      Nothing -> -1
      Just x -> x
  in
    if Array.all (_ == Nothing) arr then Nothing
    else Just (map toInt arr)

comparable :: forall f. Ord f => PrimeField f => SerdeHex f => Circuit f -> ComparableCircuit
comparable c =
  { publicInputSize: c.publicInputSize
  , gates: map
      ( \g ->
          { kind: gateKindToString g.kind
          , wires: g.wires
          , variables: varsToMaybe g.variables
          , coeffs: map toSignedDecimal g.coeffs
          , context: g.context
          }
      )
      c.gates
  , cachedConstants: Array.sortWith _.variable $ map (\cc -> { variable: cc.variable, varType: cc.varType, value: toSignedDecimal cc.value }) c.cachedConstants
  }

--------------------------------------------------------------------------------
-- Types

type GateData f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , variables :: Vector 15 (Maybe Int)
  , coeffs :: Array f
  , context :: Array String
  }

type CachedConstant f =
  { variable :: Int
  , varType :: String
  , value :: f
  }

type Circuit f =
  { publicInputSize :: Int
  , gates :: Array (GateData f)
  , cachedConstants :: Array (CachedConstant f)
  }

--------------------------------------------------------------------------------
-- From compiled PureScript circuit

fromCompiledCircuit
  :: forall f g
   . CircuitGateConstructor f g
  => PrimeField f
  => Ord f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Circuit f
fromCompiledCircuit s =
  let
    gd = makeGateData @f
      { constraints: concatMap (toKimchiRows <<< _.constraint) s.constraints
      , publicInputs: s.publicInputs
      , unionFind: (un AuxState s.aux).wireState.unionFind
      }

    contexts = piContexts <> gateContexts
      where
      piContexts = replicate (Array.length s.publicInputs) []
      gateContexts = concatMap
        (\lc -> replicate (Array.length (toKimchiRows lc.constraint :: Array (KimchiRow f))) lc.context)
        s.constraints

    gates = Array.mapWithIndex
      ( \i row ->
          let
            gateWires = circuitGateGetWires (gd.gates `unsafeIdx` i)
            wires = Array.mapWithIndex
              ( \j _ ->
                  let
                    w = gateWiresGetWire gateWires j
                  in
                    { row: wireGetRow w, col: wireGetCol w }
              )
              (Array.replicate 7 unit)
            variables = map (map getVariable) row.variables
            context = case Array.index contexts i of
              Just ctx -> ctx
              Nothing -> []
          in
            { kind: row.kind
            , wires
            , variables
            , coeffs: row.coeffs
            , context
            }
      )
      gd.constraints

    AuxState aux = s.aux
    cachedConstants =
      Array.sortWith (_.variable)
        $ map
            ( \(Tuple fieldVal var) ->
                { variable: getVariable var
                , varType: if Set.member var aux.wireState.internalVariables then "internal" else "external"
                , value: fieldVal
                }
            )
        $ (Map.toUnfoldable aux.wireState.cachedConstants :: Array _)
  in
    { publicInputSize: gd.publicInputSize
    , gates
    , cachedConstants
    }
  where
  unsafeIdx :: forall a. Array a -> Int -> a
  unsafeIdx arr i = case Array.index arr i of
    Just x -> x
    Nothing -> unsafeCrashWith ("fromCompiledCircuit: gate index out of bounds: " <> show i)

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
