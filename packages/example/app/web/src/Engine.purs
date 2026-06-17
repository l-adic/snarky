-- | The browser engine: the one-block pipeline — SRS + compile, genesis, random
-- | transfers, base + merge proofs through the snark manager, root-proof
-- | verification — emitting typed events through `EngineCallbacks` instead of
-- | touching any UI. Driven by the P2P coordinator (`Snarky.Example.P2P.Backend`
-- | / `Snarky.Example.Web.P2P.Worker`) over an injected `SnarkBackend`.
-- |
-- | Runs inside a Web Worker over the wasm kimchi backend: proving is
-- | synchronous, so it must never live on the UI thread.
module Snarky.Example.Web.Engine
  ( Depth
  , EngineCallbacks
  , ScanView
  , TxView
  , runWith
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds)
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
import Snarky.Example.Snark.Pool (PoolSize)
import Snarky.Example.Snark.Progress (scanStateView)
import Snarky.Example.Snark.Worker (SnarkBackend)
import Snarky.Example.Srs.Cache (nullCache)
import Snarky.Example.Transaction (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types.PublicKey (toBase58Check)

-- | Ledger tree depth, matching the terminal entry.
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

type ScanView =
  { blockId :: Int
  , leaves :: Int
  , statuses :: Array { slot :: Int, status :: String }
  }

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

-- | The engine parameterized by its snark backend (plus pool size / job
-- | timeout): the P2P coordinator drives the one-block pipeline over a `Dynamic`
-- | pool whose first worker is its own in-process prover and the rest are remote
-- | peers (`Snarky.Example.P2P.Backend.p2pSnarkBackend`).
runWith :: SnarkBackend Depth -> PoolSize -> Milliseconds -> EngineCallbacks -> Effect Unit
runWith backend poolSize jobTimeout cb = launchAff_ do
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
    , poolSize
    , jobTimeout
    , backend
    -- Browser SRS caching (IndexedDB) is deferred; the engine builds un-cached.
    , cache: nullCache
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
