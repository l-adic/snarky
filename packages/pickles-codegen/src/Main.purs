-- | Code generation main entry point
-- | Reads JSON linearization files and generates PureScript modules
module Pickles.Linearization.Main where

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
import Pickles.Linearization.Generator (CurveName(..), generateModule)
import Pickles.Linearization.Types (Linearization)
import Simple.JSON (readJSON)

main :: Effect Unit
main = launchAff_ do
  -- Read input/output directories from environment variables
  inputDir <- liftEffect $ Process.lookupEnv "LINEARIZATION_JSON_DIR" >>= case _ of
    Nothing -> throw "LINEARIZATION_JSON_DIR environment variable not set"
    Just dir -> pure dir

  outputDir <- liftEffect $ Process.lookupEnv "LINEARIZATION_OUTPUT_DIR" >>= case _ of
    Nothing -> throw "LINEARIZATION_OUTPUT_DIR environment variable not set"
    Just dir -> pure dir

  -- Parse and generate Pallas scalar field linearization
  let pallasJsonPath = Path.concat [ inputDir, "pallas_scalar_field.json" ]
  Console.log $ "Reading " <> pallasJsonPath
  pallasContent <- readTextFile UTF8 pallasJsonPath
  case readJSON pallasContent :: _ Linearization of
    Left errs -> Console.log $ "Pallas decode error: " <> show errs
    Right pallas -> do
      Console.log $ "Pallas: parsed " <> show (Array.length pallas.constant_term) <> " tokens in constant_term"
      let pallasModule = generateModule Pallas pallas
      let pallasOutputPath = Path.concat [ outputDir, "Pallas.purs" ]
      Console.log $ "Writing " <> pallasOutputPath
      writeTextFile UTF8 pallasOutputPath pallasModule
      Console.log $ "Pallas module generated successfully (" <> show (Array.length pallas.constant_term) <> " tokens)"

  -- Parse and generate Vesta scalar field linearization
  let vestaJsonPath = Path.concat [ inputDir, "vesta_scalar_field.json" ]
  Console.log $ "Reading " <> vestaJsonPath
  vestaContent <- readTextFile UTF8 vestaJsonPath
  case readJSON vestaContent :: _ Linearization of
    Left errs -> Console.log $ "Vesta decode error: " <> show errs
    Right vesta -> do
      Console.log $ "Vesta: parsed " <> show (Array.length vesta.constant_term) <> " tokens in constant_term"
      let vestaModule = generateModule Vesta vesta
      let vestaOutputPath = Path.concat [ outputDir, "Vesta.purs" ]
      Console.log $ "Writing " <> vestaOutputPath
      writeTextFile UTF8 vestaOutputPath vestaModule
      Console.log $ "Vesta module generated successfully (" <> show (Array.length vesta.constant_term) <> " tokens)"
