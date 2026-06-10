-- | The snark-work protocol shared by the block producer and the worker: the
-- | unit of work and the proof it yields. Both ends depend only on this module,
-- | so the channel boundary between them is explicit.
-- |
-- | NOTE: for now `WorkItem` carries typed values directly (the witness mask,
-- | the prev proofs). When the worker moves cross-process, these fields become
-- | the serialized forms and this module grows the codecs — the producer and
-- | worker don't change, only the transport.
module Snarky.Example.Snark.Work
  ( WorkItem(..)
  , BaseJob
  , Proof
  ) where

import Pickles (CompiledProof)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction (SignedTransaction, Statement, TxnStmt)

-- | The per-transaction witness: a mask keyed by public key (so the circuit's
-- | `getAccountId` resolves against it), over the example's `Account` leaves.

-- | A proof of the two-branch transaction-snark program (base or merge — same
-- | wrap VK, both `CompiledProof 2 TxnStmt`).
type Proof = CompiledProof 2 TxnStmt

-- | One base-proof job: the transaction, its witness, and its statement
-- | (`{ source = root Lᵢ, target = root Lᵢ₊₁ }`). What `processBlock` emits per
-- | transaction, and what a `Leaf` of the scan-state tree holds.
type BaseJob d =
  { tx :: SignedTransaction Vesta.ScalarField
  , mask :: Mask d
  , statement :: Statement Vesta.ScalarField
  }

-- | A unit of snark work: either prove a base transaction against its witness,
-- | or merge two child proofs.
data WorkItem d
  = Base (BaseJob d)
  | Merge
      { proof1 :: Proof
      , proof2 :: Proof
      , statement :: Statement Vesta.ScalarField
      }
