module Example.FixtureDump.Application (Depth, FixtureApplication, compileFixture) where

import Prelude

import Data.Either (either)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (tuple2)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Mina.ChainId (ChainId(..))
import Pickles (BranchProver(..), SlotWrapKey(..), compileMulti, mkRuleEntry, provedPrev)
import Snarky.Backend.Kimchi.Impl.Pallas as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta as Vesta
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.Types (NoOutput)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Example.Env (pallasSrsSize, vestaSrsSize)
import Snarky.Example.Ledger (Mask, emptyMask)
import Snarky.Example.Transaction (CompiledTx, TransferAdvice, baseRule, mergeRule, runTransferMaskM)
import Snarky.Lagrange.Cache.FS (defaultDir, fsCache)

type Depth = 4

type FixtureApplication =
  { srs :: { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG }
  , compiled :: CompiledTx Depth
  }

compileFixture :: Maybe String -> String -> Effect FixtureApplication
compileFixture dump cache = do
  lagrangeCache <- fsCache <$> defaultDir
  let
    srs =
      { pallasSrs: Pallas.pallasCrsCreate pallasSrsSize
      , vestaSrs: Vesta.vestaCrsCreate vestaSrsSize
      }
  baseEntry <- mkRuleEntry @NoOutput @(TransferAdvice Depth) (baseRule @Depth Testnet) Vector.nil
  mergeEntry <- mkRuleEntry @NoOutput @(TransferAdvice Depth) mergeRule (Self :< Self :< Vector.nil)
  out <- compileMulti @NoOutput @1
    { srs
    , debug: false
    , wrapDomainOverride: Just 14
    , proofCache: Just (mkProofCache cache)
    , lagrangeCache: Just lagrangeCache
    , dump
    }
    (tuple2 baseEntry mergeEntry)
  let
    BranchProver proveBase = fst out.provers
    BranchProver proveMerge = fst (snd out.provers)
  pure
    { srs
    , compiled:
        { baseProver: \{ env, statement } -> do
            mask <- Ref.new env.mask
            proveBase (runTransferMaskM { currentTransaction: Just env.tx, mask })
              { appInput: statement, prevs: unit } >>= either (throw <<< show) pure
        , mergeProver: \{ statement, proof1, proof2 } -> do
            mask <- Ref.new (emptyMask :: Mask Depth)
            proveMerge (runTransferMaskM { currentTransaction: Nothing, mask })
              { appInput: statement
              , prevs: tuple2 (provedPrev proof1) (provedPrev proof2)
              } >>= either (throw <<< show) pure
        , verifier: out.verifier
        }
    }
