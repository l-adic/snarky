module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Exception (throw)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile, writeTextFile)
import Node.Path as Path
import Node.Process as Process
import Pickles.CircuitDiffs.OcamlCircuit (OcamlCircuit, parseOcamlCircuit)
import Simple.JSON (write)
import Snarky.Curves.Pallas as Pallas

foreign import prettyJSON :: forall a. a -> String

main :: Effect Unit
main = launchAff_ do
  circuitsDir <- liftEffect $ Process.lookupEnv "CIRCUITS_DIR" >>= case _ of
    Nothing -> throw "CIRCUITS_DIR environment variable not set"
    Just dir -> pure dir

  name <- liftEffect $ Process.lookupEnv "CIRCUIT_NAME" >>= case _ of
    Nothing -> throw "CIRCUIT_NAME environment variable not set"
    Just n -> pure n

  let
    base = Path.concat [ circuitsDir, name ]
    circuitPath = base <> ".json"
    cachedPath = base <> "_cached_constants.json"
    gateLabelsPath = base <> "_gate_labels.jsonl"

  Console.log $ "Reading " <> name <> " from " <> circuitsDir
  circuit <- readTextFile UTF8 circuitPath
  cachedConstants <- readTextFile UTF8 cachedPath
  gateLabels <- readTextFile UTF8 gateLabelsPath

  let
    result :: _ (OcamlCircuit Pallas.ScalarField)
    result = parseOcamlCircuit { circuit, cachedConstants, gateLabels }
  case result of
    Left errs -> liftEffect $ throw $ "Parse error: " <> show errs
    Right parsed -> do
      Console.log $ "Parsed " <> name <> ":"
      Console.log $ "  gates: " <> show (Array.length parsed.gates)
      Console.log $ "  cachedConstants: " <> show (Array.length parsed.cachedConstants)
      Console.log $ "  publicInputSize: " <> show parsed.publicInputSize

      let outPath = "/tmp/parsed_" <> name <> ".json"
      writeTextFile UTF8 outPath (serializeCircuit parsed)
      Console.log $ "Wrote to " <> outPath

serializeCircuit :: OcamlCircuit Pallas.ScalarField -> String
serializeCircuit c =
  prettyJSON $ write
    { publicInputSize: c.publicInputSize
    , gates: map serializeGate c.gates
    , cachedConstants: map serializeCachedConstant c.cachedConstants
    }
  where
  serializeGate g =
    { kind: show g.kind
    , wires: g.wires
    , coeffs: map show g.coeffs
    , context: g.context
    }
  serializeCachedConstant cc =
    { variable: cc.variable
    , value: show cc.value
    }
