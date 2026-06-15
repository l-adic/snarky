-- | The terminal-wasm entry: drives the SAME shared `runSimulation`
-- | (`Snarky.Example.Engine`) the browser uses, but wires its events to the
-- | terminal — logs to stdout, the scan-state tree to the pinned display.
-- |
-- | This is purely a UI adapter; nothing here is wasm-specific. The wasm
-- | backend is selected at the process level by `KIMCHI_BACKEND=wasm` (see
-- | `kimchi-napi/index.js`, which loads the wasm node loader and sizes its
-- | rayon pool at require time), so the same code runs native too. Launched
-- | by `tools/run_simulation_wasm.sh`.
module Snarky.Example.WasmMain
  ( main
  ) where

import Prelude

import Colog (Msg(..), Severity(..), richMessageStdout, unLogAction)
import Data.Foldable (for_)
import Effect (Effect)
import Fmt (fmt)
import Node.Process (exit')
import Snarky.Example.Engine (runSimulation)
import Snarky.Example.Snark.Progress (renderScanView)
import Snarky.Example.Terminal.ProgressDisplay (mkProgressDisplay)

parseSeverity :: String -> Severity
parseSeverity = case _ of
  "debug" -> Debug
  "warning" -> Warning
  "error" -> Error
  _ -> Info

main :: Effect Unit
main = do
  display <- mkProgressDisplay
  let
    logger = display.wrapLogger richMessageStdout
    logAt severity text = unLogAction logger (Msg { severity, text })
  runSimulation
    { onLog: \{ severity, text } -> logAt (parseSeverity severity) text
    , onPhase: \phase -> logAt Info (fmt @"[phase] {phase}" { phase })
    , onTxs: \txs -> for_ txs \t ->
        logAt Info (fmt @"tx (nonce {nonce}): {from} -> {to}, amount {amount}" t)
    , onScan: \v -> display.paint (renderScanView v)
    , onVerified: \ok -> do
        if ok then logAt Info "root proof verified — block accepted"
        else logAt Error "root proof FAILED to verify — block rejected"
        display.done
        exit' 0
    }
