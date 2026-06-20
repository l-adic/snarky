module Test.Snarky.Lagrange.Main where

import Prelude

import Effect (Effect)
import Test.Snarky.Lagrange.CacheSpec as CacheSpec
import Test.Snarky.Lagrange.FsCacheSpec as FsCacheSpec
import Test.Snarky.Lagrange.HydratedSpec as HydratedSpec
import Test.Snarky.Lagrange.IdbSpec as IdbSpec
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    CacheSpec.spec
    FsCacheSpec.spec
    HydratedSpec.spec
    IdbSpec.spec
