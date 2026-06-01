module Test.Example.Main where

import Prelude

import Effect (Effect)
import Test.Snarky.Example.Circuits as Circuits
import Test.Snarky.Example.TransactionSnark as TransactionSnark
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    Circuits.spec
    TransactionSnark.spec
