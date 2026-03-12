module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Pickles.CircuitDiffs (greeting)

main :: Effect Unit
main = log greeting
