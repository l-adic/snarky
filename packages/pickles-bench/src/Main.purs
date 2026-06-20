-- | Entry point for the pickles benchmark suite.
-- |
-- | Owns the *shared, untimed* setup, then hands a `Group[]` to the shared
-- | `bench-harness` runner (`Bench.Harness.runBench`) — the SAME runner the o1js
-- | suite uses. No `benchlib`: the runner, GC/window instrumentation, stats, and
-- | artifact all live in the central JS lib; the napi FFI split is this site's
-- | own instrumentation (`Bench.Pickles.Ffi`), passed as hooks.
-- |
-- | Shared setup runs ONCE here, excluded from every measured region:
-- |   * `installFfiWrappers` / `FfiTimer.install` monkey-patch the cached
-- |     `kimchi-napi` singleton (idempotent; counters inert until a hook arms
-- |     them).
-- |   * `mkBenchSrs` builds the SRSes + pre-warms the lagrange cache.
-- | The prove group's own `prepare` (compile + b0) runs when `runBench` reaches
-- | it — AFTER the compile group — so compile is never measured with prove's
-- | prepared state resident.
-- |
-- | CLI: `--only compile | prove` runs ONLY the named group. `--help` for usage.
-- |
-- | This package is its OWN spago workspace (purs-backend-es). Run via the
-- | `tools/bench.sh` launcher (build -> output-es/, then node-run `run.mjs`).
module Bench.Pickles.Main where

import Prelude

import Bench.Harness as Harness
import Bench.Pickles.Common (mkBenchSrs)
import Bench.Pickles.Compile as Compile
import Bench.Pickles.Ffi as Ffi
import Bench.Pickles.FfiTimer as FfiTimer
import Bench.Pickles.Prove as Prove
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), optional)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Options.Applicative ((<**>))
import Options.Applicative as Opt

-- | The two bench groups the suite knows about.
data BenchGroup = Compile | Prove

derive instance Eq BenchGroup

-- | `--only <group>` argument parser.
parseGroup :: String -> Either String BenchGroup
parseGroup = case _ of
  "compile" -> Right Compile
  "prove" -> Right Prove
  s -> Left ("unknown group '" <> s <> "' (expected: compile | prove)")

type CliOptions = { only :: Maybe BenchGroup }

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

  -- One-time, untimed, shared setup (see module note).
  Ffi.installFfiWrappers
  FfiTimer.install
  srs <- mkBenchSrs

  -- Build both groups; selection just drops one. Order is [compile, prove] so
  -- prove's prepare (which leaves state resident) runs after the compile group.
  proveGroup <- Prove.group srs
  let
    compileGroup = Compile.group srs
    wants g = case opts.only of
      Nothing -> true
      Just sel -> sel == g
    groups =
      (if wants Compile then [ compileGroup ] else [])
        <> (if wants Prove then [ proveGroup ] else [])
    hooks = { onStart: Ffi.onStart, onEnd: Ffi.onEnd }

  launchAff_ do
    benches <- Harness.runBench groups hooks
    augmented <- liftEffect (Ffi.attachFfi benches)
    liftEffect (Harness.writeArtifact { suite: "pickles", benches: augmented })
