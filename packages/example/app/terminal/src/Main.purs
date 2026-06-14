-- | The simulation entry point: build a `Simulation` (SRS + circuit compile,
-- | genesis ledger, snark manager), then drive one block through the full
-- | pipeline — generate random transfers, extract per-transaction snark work,
-- | farm it to the manager, and on a verified root proof adopt the new ledger.
-- |
-- | The scan-state progress display pins a live work tree to the bottom of
-- | the terminal (logs scroll above it).
module Snarky.Example.Main
  ( main
  ) where

import Prelude

import Colog (richMessageStdout)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Mina.ChainId (ChainId(..))
import Pickles (toVerifiable, verifyBatch)
import Snarky.Example.Block (Block(..), processBlock)
import Snarky.Example.Ledger (balanceOf)
import Snarky.Example.Log as Log
import Snarky.Example.Simulation (generateBlock, mkSimulation)
import Snarky.Example.Snark.Manager (submitBlock)
import Snarky.Example.Terminal.ProgressDisplay (mkProgressDisplay)
import Snarky.Example.Transaction (SignedTransaction(..), Transaction(..), Transfer(..))

-- | Ledger tree depth for the simulation (2^4 = 16 account slots).
type Depth = 4

main :: Effect Unit
main = launchAff_ do
  display <- liftEffect mkProgressDisplay
  let logger = display.wrapLogger richMessageStdout
  sim <- mkSimulation @Depth
    { chainId: Testnet, numAccounts: 10, logger, onProgress: Just display.reporter }

  -- One block of random transfers against the current ledger.
  ledger0 <- liftEffect $ Ref.read sim.env.ledger
  block@(Block { transactions }) <- liftEffect $ generateBlock sim.env.chainId sim.keys ledger0
  for_ transactions \(SignedTransaction { transaction: Transaction { nonce, transfer: Transfer { from, to, amount } } }) ->
    Log.logInfo logger $ fmt
      @"[Main] tx (nonce {nonce}): {from} -> {to}, amount {amount}"
      { nonce: show nonce, from: show from, to: show to, amount: show (balanceOf amount) }

  -- Phase 1: the sequential witness-extraction fold; Phase 2: farm the work
  -- to the snark manager and await the block's root proof.
  { ledger: ledger1, snarkWork } <- liftEffect $ processBlock sim.env.chainId ledger0 block
  rootProof <- submitBlock sim.manager 0 snarkWork

  -- Accept the block: verify the root proof, then adopt the new ledger.
  if verifyBatch sim.env.compiledTx.verifier [ toVerifiable rootProof ] then do
    liftEffect $ Ref.write ledger1 sim.env.ledger
    Log.logInfo logger "[Main] root proof verified — block accepted, ledger advanced"
  else
    Log.logError logger "[Main] root proof FAILED to verify — block rejected"

  -- Persist the final frame of the progress display.
  liftEffect display.done
