module Test.Pickles.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.Commitments as Commitments
import Test.Pickles.E2E as E2E
import Test.Pickles.IPA as IPA
import Test.Pickles.Linearization as Linearization
import Test.Pickles.Permutation as Permutation
import Test.Spec (mapSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    E2E.spec
    mapSpec nat do
      Commitments.spec
      IPA.spec
      Linearization.spec
      Permutation.spec
  where
  nat :: Identity ~> Aff
  nat x = pure $ un Identity x
