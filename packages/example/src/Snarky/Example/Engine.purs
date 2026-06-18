-- | The one-block engine pipeline, decoupled from any UI or browser: given a
-- | ready `Simulation` (compiled program + manager + genesis keys), `runEngine`
-- | generates a block, proves it through the manager to a root proof, verifies
-- | that root, and emits typed events (`EngineCallbacks`) along the way. It is
-- | pure orchestration over lib pieces (no DOM, no Web Worker, no SRS cache), so
-- | the whole coordinator behavior is exercisable in Node — the browser entry
-- | (`Snarky.Example.Web.Engine.runWith`) only adds the setup (SRS cache + compile)
-- | and the `runAff_` shell on top.
module Snarky.Example.Engine
  ( EngineCallbacks
  , TxView
  , ScanView
  , txHash
  , txView
  , scanView
  , severityLabel
  , engineLogger
  , engineOnProgress
  , runEngine
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Pickles (toVerifiable, verifyBatch)
import Snarky.Circuit.RandomOracle (Digest(..), hashOf)
import Snarky.Curves.Class (toHexLe)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Block (Block(..), processBlock)
import Snarky.Example.Ledger (balanceOf)
import Snarky.Example.Log (Logger)
import Snarky.Example.Simulation (Simulation, generateBlock)
import Snarky.Example.Snark.Manager (BlockId, OnProgress, submitBlock)
import Snarky.Example.Snark.Progress (scanStateView)
import Snarky.Example.Snark.ScanState (ScanState)
import Snarky.Example.Transaction (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types.PublicKey (toBase58Check)

-- | A transaction row for the UI: its identity hash plus the human fields.
type TxView = { hash :: String, nonce :: String, from :: String, to :: String, amount :: String }

-- | A snapshot of a block's scan-state tree for the UI: the leaf count and each
-- | heap slot's status ("complete" | "pending" | "locked").
type ScanView =
  { blockId :: Int
  , leaves :: Int
  , statuses :: Array { slot :: Int, status :: String }
  }

-- | The events the engine emits; the caller (browser UI, or a Node test capturing
-- | them) decides what to do with each. Severity arrives pre-rendered as a label
-- | so the sink needs no colog dependency.
type EngineCallbacks =
  { onLog :: { severity :: String, text :: String } -> Effect Unit
  , onPhase :: String -> Effect Unit
  , onTxs :: Array TxView -> Effect Unit
  , onScan :: ScanView -> Effect Unit
  , onVerified :: Boolean -> Effect Unit
  }

-- | The transaction hash shown as the row's identity: the Poseidon digest of the
-- | transaction (the same field the signature signs over), hex-encoded.
txHash :: Transaction Vesta.ScalarField -> String
txHash transaction =
  let
    Digest h = hashOf transaction :: Digest Vesta.ScalarField
  in
    toHexLe h

-- | Project a signed transaction to its display row.
txView :: SignedTransaction Vesta.ScalarField -> TxView
txView (SignedTransaction { transaction: tx@(Transaction { nonce, transfer: Transfer { from, to, amount } }) }) =
  { hash: txHash tx
  , nonce: show nonce
  , from: toBase58Check from
  , to: toBase58Check to
  , amount: show (balanceOf amount)
  }

-- | Project a block's scan state to its display snapshot.
scanView :: forall d. BlockId -> ScanState d -> ScanView
scanView blockId st =
  let
    v = scanStateView st
  in
    { blockId, leaves: v.leaves, statuses: v.statuses }

-- | The label `EngineCallbacks.onLog` expects for a colog `Severity`.
severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"

-- | A colog `Logger` that relays every message to `onLog` (severity → label).
engineLogger :: EngineCallbacks -> Logger
engineLogger cb = LogAction \(Msg { severity, text }) ->
  cb.onLog { severity: severityLabel severity, text }

-- | The manager progress observer that drives `onScan` (wire this into the
-- | `Simulation`/manager so scan snapshots reach the UI as the block proves).
engineOnProgress :: forall d. EngineCallbacks -> OnProgress d
engineOnProgress cb = \blockId st -> cb.onScan (scanView blockId st)

-- | Run the one-block pipeline over a ready `Simulation`: generate a block (→
-- | `onTxs`), prove it to a root, verify the root (→ `onVerified`), and commit the
-- | ledger on success. Phases are reported through `onPhase`; scan-state snapshots
-- | arrive via the manager's `engineOnProgress` during proving. Setup (SRS +
-- | compile, i.e. building the `Simulation`) is the caller's responsibility.
runEngine :: forall d. Reflectable d Int => Simulation d -> EngineCallbacks -> Aff Unit
runEngine sim cb = do
  liftEffect $ cb.onPhase "block"
  ledger0 <- liftEffect $ Ref.read sim.env.ledger
  block@(Block { transactions }) <- liftEffect $ generateBlock sim.env.chainId sim.keys ledger0
  liftEffect $ cb.onTxs $ Vector.toUnfoldable $ map txView transactions

  liftEffect $ cb.onPhase "proving"
  { ledger: ledger1, snarkWork } <- liftEffect $ processBlock sim.env.chainId ledger0 block
  rootProof <- submitBlock sim.manager 0 snarkWork

  if verifyBatch sim.env.compiledTx.verifier [ toVerifiable rootProof ] then do
    liftEffect $ Ref.write ledger1 sim.env.ledger
    liftEffect $ cb.onVerified true
  else
    liftEffect $ cb.onVerified false
  liftEffect $ cb.onPhase "done"
