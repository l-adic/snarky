-- | The UI-agnostic simulation engine: the one-block pipeline — SRS +
-- | compile, genesis, random transfers, base + merge proofs through the
-- | snark manager, root-proof verification — emitting typed events through
-- | `EngineCallbacks` instead of touching any UI.
-- |
-- | Both frontends drive the SAME `runSimulation`: the terminal-wasm entry
-- | (`Snarky.Example.WasmMain`) wires the callbacks to stdout + the pinned
-- | display; the browser worker (web/worker-entry.js) wires them to
-- | `postMessage` and the UI thread renders them. Proving is synchronous, so
-- | this must run off any UI thread (a process, or a worker).
module Snarky.Example.Engine
  ( EngineCallbacks
  , TxView
  , runSimulation
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Mina.ChainId (ChainId(..))
import Pickles (toVerifiable, verifyBatch)
import Snarky.Circuit.RandomOracle (Digest(..), hashOf)
import Snarky.Curves.Class (toHexLe)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Block (Block(..), processBlock)
import Snarky.Example.Ledger (balanceOf)
import Snarky.Example.Simulation (generateBlock, mkSimulation)
import Snarky.Example.Snark.Manager (submitBlock)
import Snarky.Example.Snark.Progress (ScanView, scanStateView)
import Snarky.Example.Snark.Worker (localSnarkBackend)
import Snarky.Example.Transaction (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types.PublicKey (toBase58Check)

-- | Ledger tree depth (matches the native terminal entry).
type Depth = 4

type TxView = { hash :: String, nonce :: String, from :: String, to :: String, amount :: String }

-- | The transaction hash shown as the row's identity: the Poseidon
-- | digest of the transaction (the same field the signature signs over),
-- | hex-encoded.
txHash :: Transaction Vesta.ScalarField -> String
txHash transaction =
  let
    Digest h = hashOf transaction :: Digest Vesta.ScalarField
  in
    toHexLe h

-- | The UI-agnostic events the engine emits (all payloads serializable, so
-- | they survive a worker `postMessage`).
type EngineCallbacks =
  { onLog :: { severity :: String, text :: String } -> Effect Unit
  , onPhase :: String -> Effect Unit
  , onTxs :: Array TxView -> Effect Unit
  , onScan :: ScanView -> Effect Unit
  , onVerified :: Boolean -> Effect Unit
  }

severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"

runSimulation :: EngineCallbacks -> Effect Unit
runSimulation cb = launchAff_ do
  let
    logger = LogAction \(Msg { severity, text }) ->
      cb.onLog { severity: severityLabel severity, text }
    onProgress = \blockId st ->
      let
        v = scanStateView st
      in
        cb.onScan { blockId, leaves: v.leaves, statuses: v.statuses }

  liftEffect $ cb.onPhase "setup"
  sim <- mkSimulation @Depth
    { chainId: Testnet
    , numAccounts: 10
    , logger
    , onProgress: Just onProgress
    , poolSize: 1
    -- Unused by the in-process backend (its synchronous run never times out).
    , jobTimeout: Milliseconds 120000.0
    , backend: localSnarkBackend
    }

  liftEffect $ cb.onPhase "block"
  ledger0 <- liftEffect $ Ref.read sim.env.ledger
  block@(Block { transactions }) <- liftEffect $ generateBlock sim.env.chainId sim.keys ledger0
  liftEffect $ cb.onTxs $ Vector.toUnfoldable $ transactions <#>
    \(SignedTransaction { transaction: tx@(Transaction { nonce, transfer: Transfer { from, to, amount } }) }) ->
      { hash: txHash tx
      , nonce: show nonce
      , from: toBase58Check from
      , to: toBase58Check to
      , amount: show (balanceOf amount)
      }

  liftEffect $ cb.onPhase "proving"
  { ledger: ledger1, snarkWork } <- liftEffect $ processBlock sim.env.chainId ledger0 block
  rootProof <- submitBlock sim.manager 0 snarkWork

  if verifyBatch sim.env.compiledTx.verifier [ toVerifiable rootProof ] then do
    liftEffect $ Ref.write ledger1 sim.env.ledger
    liftEffect $ cb.onVerified true
  else
    liftEffect $ cb.onVerified false
  liftEffect $ cb.onPhase "done"
