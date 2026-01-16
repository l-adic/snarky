module Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Pickles.Linearization.Types (Linearization)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile)
import Node.Path as Path
import Node.Process as Process
import Simple.JSON (readJSON)

main :: Effect Unit
main = launchAff_ do
  cwd <- liftEffect Process.cwd

  -- Parse Pallas scalar field linearization
  let pallasPath = Path.concat [ cwd, "packages", "snarky-kimchi", "generated", "pallas_scalar_field.json" ]
  Console.log $ "Reading " <> pallasPath
  pallasContent <- readTextFile UTF8 pallasPath
  case readJSON pallasContent :: _ Linearization of
    Left errs -> Console.log $ "Pallas decode error: " <> show errs
    Right pallas -> do
      Console.log $ "Pallas: ok (" <> show (Array.length pallas.constant_term) <> " tokens in constant_term)"

  -- Parse Vesta scalar field linearization
  let vestaPath = Path.concat [ cwd, "packages", "snarky-kimchi", "generated", "vesta_scalar_field.json" ]
  Console.log $ "Reading " <> vestaPath
  vestaContent <- readTextFile UTF8 vestaPath
  case readJSON vestaContent :: _ Linearization of
    Left errs -> Console.log $ "Vesta decode error: " <> show errs
    Right vesta -> do
      Console.log $ "Vesta: ok (" <> show (Array.length vesta.constant_term) <> " tokens in constant_term)"
