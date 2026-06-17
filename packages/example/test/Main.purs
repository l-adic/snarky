module Test.Example.Main where

import Prelude

import Colog (richMessageStdout)
import Effect (Effect)
import Effect.Class (liftEffect)
import Snarky.Example.Env (mkConfig, mkEnv)
import Test.Snarky.Example.Block as Block
import Test.Snarky.Example.Circuits as Circuits
import Test.Snarky.Example.Config (Depth, chainId)
import Test.Snarky.Example.P2P.BusSpec as BusSpec
import Test.Snarky.Example.P2P.CoordinatorSpec as CoordinatorSpec
import Test.Snarky.Example.P2P.PipelineSpec as PipelineSpec
import Test.Snarky.Example.Snark.PoolSpec as PoolSpec
import Test.Snarky.Example.Srs.CacheSpec as SrsCacheSpec
import Test.Snarky.Example.Srs.FsCacheSpec as FsCacheSpec
import Test.Snarky.Example.TransactionSnark as TransactionSnark
import Test.Spec (beforeAll)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    Circuits.spec
    -- Pool reliability + the in-memory transport bus — in-process, no Env needed.
    PoolSpec.spec
    BusSpec.spec
    CoordinatorSpec.spec
    SrsCacheSpec.spec
    FsCacheSpec.spec
    -- One Env (SRS build + circuit compile) shared by every pickled test.
    beforeAll (liftEffect (mkEnv @Depth richMessageStdout =<< mkConfig chainId)) do
      TransactionSnark.spec
      Block.spec
      -- Real-proof block pipeline driven over the in-memory P2P transport.
      PipelineSpec.spec
