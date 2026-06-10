-- | Entry point for the pickles benchmark suite.
-- |
-- | This module owns the *shared, untimed* setup and aggregates every
-- | bench target into a single benchlib `suite`. Each target lives in
-- | its own module and exports a `group`:
-- |   * `Bench.Pickles.Compile` — full N=2 compilation (NRR + tree).
-- |   * `Bench.Pickles.Prove`   — one recursive N=2 tree prove (b1).
-- | The shared circuit + the warmed SRS live in `Bench.Pickles.Common`.
-- |
-- | Shared setup runs ONCE here, before the suite, so it is excluded
-- | from every measured region:
-- |   * `mkBenchSrs` builds one SRS pair and pre-warms its lagrange
-- |     cache (the cache lives inside the SRS object, so every group
-- |     reusing this record pays nothing for SRS load or lagrange).
-- |   * `Prove.prepareProve` does the prove bench's compile + b0 once
-- |     (NOT via benchlib's `prepareInput`, which re-runs per iteration).
-- |
-- | CLI: `--only compile | prove` runs ONLY the named group. The other
-- | group's setup (notably `Prove.prepareProve`, which is itself a full
-- | compile + b0) is skipped, so `--only compile` doesn't pay for the
-- | prove warmup and `--only prove` doesn't run the timed compile.
-- | `--help` prints the parser usage.
-- |
-- | This package is its OWN spago workspace (its spago.yaml has a
-- | `workspace:` section, so the root workspace ignores it). Only this
-- | workspace uses purs-backend-es. Run via the `tools/bench.sh` launcher
-- | (it `cd`s here, build → purs-backend-es → output-es/, then
-- | `node`-run the optimized entrypoint). NOT `spago run`: the
-- | purs-backend-es backend makes spago mis-invoke it as a runner.
module Bench.Pickles.Main where

import Prelude

import Bench.Pickles.BenchUtils as BenchUtils
import Bench.Pickles.Common (mkBenchSrs)
import Bench.Pickles.Compile as Compile
import Bench.Pickles.FfiTimer as FfiTimer
import Bench.Pickles.Prove as Prove
import Bench.Pickles.Report (jsonReporter)
import Bench.Pickles.Stats (statsReporter)
import BenchLib (reportConsole, runNode, suite)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (elem)
import Data.Maybe (Maybe(..), optional)
import Effect (Effect)
import Options.Applicative ((<**>))
import Options.Applicative as Opt

-- | The two bench groups the suite knows about.
data BenchGroup = Compile | Prove

derive instance Eq BenchGroup

allGroups :: Array BenchGroup
allGroups = [ Compile, Prove ]

-- | `--only <group>` argument parser.
parseGroup :: String -> Either String BenchGroup
parseGroup = case _ of
  "compile" -> Right Compile
  "prove" -> Right Prove
  s -> Left ("unknown group '" <> s <> "' (expected: compile | prove)")

type CliOptions =
  { only :: Maybe BenchGroup
  }

cliParser :: Opt.Parser CliOptions
cliParser = ado
  only <- optional $ Opt.option (Opt.eitherReader parseGroup)
    ( Opt.long "only"
        <> Opt.metavar "GROUP"
        <> Opt.help "Run only the named group: compile | prove"
    )
  in { only }

cliInfo :: Opt.ParserInfo CliOptions
cliInfo = Opt.info (cliParser <**> Opt.helper)
  ( Opt.fullDesc
      <> Opt.progDesc "Pickles benchmark suite (compile + prove)"
      <> Opt.header "pickles-bench"
  )

main :: Effect Unit
main = do
  opts <- Opt.execParser cliInfo
  let
    selected = case opts.only of
      Nothing -> allGroups
      Just g -> [ g ]

  -- One-time, untimed, shared across whatever subset is selected.
  --   * `installFfiWrappers` / `FfiTimer.install` monkey-patch the cached
  --     `kimchi-napi` singleton with timing+counter wrappers. Idempotent;
  --     wrappers stay inactive until `startFfiTracking` flips the gate
  --     (see `Compile.group` / `Prove.group`).
  --   * `mkBenchSrs` builds the SRSes and pre-warms the lagrange cache
  --     so benchlib's timed samples don't pay for either.
  BenchUtils.installFfiWrappers
  FfiTimer.install
  srs <- mkBenchSrs

  -- prepareProve is itself a full compile + b0 — only pay for it when
  -- Prove is actually going to run.
  mProveThunk <-
    if elem Prove selected then
      map Just (Prove.prepareProve srs)
    else
      pure Nothing

  let
    groups = selected # Array.mapMaybe case _ of
      Compile -> Just (Compile.group srs)
      Prove -> map Prove.group mProveThunk

  runNode (\o -> o { reporters = [ reportConsole, statsReporter, jsonReporter ] }) $
    suite "pickles"
      -- Suite-level defaults; each group overrides `iterations`.
      (\o -> o { iterations = 1, sizes = [ 0 ] })
      groups
