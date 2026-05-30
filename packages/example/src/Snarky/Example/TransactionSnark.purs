-- | The example "Transaction_snark" as a Pickles application, mirroring
-- | `mina/src/lib/transaction_snark/transaction_snark.ml` (the `Base` and
-- | `Merge` inductive rules). Statement = a {source, target} ledger-digest
-- | pair, carried as the public INPUT (public output is `()`), exactly as
-- | Mina does it (`public_input = statement`, `public_output = ()`).
-- |
-- |   * base  (mpv = 0): proves `target = processTransaction(source, tx)`
-- |     for a private signed transfer `tx`.
-- |   * merge (mpv = 2, Self): witnesses the two sub-statements s1, s2
-- |     (= the verified prev proofs' public inputs) and asserts the merge
-- |     relation `s.source = s1.source`, `s2.target = s.target`,
-- |     `s1.target = s2.source` (the connecting ledger).
-- |
-- | This is the first app to exercise app advice (`MerkleRequestM`,
-- | `AccountMapM`, `TransactionM`) inside a pickles rule. Because pickles
-- | now runs rules in the caller's bare monad `m`, those are ordinary
-- | constraints on `m`, discharged at the concrete app monad when the
-- | entry is built (`mkRuleEntry @AppM`). `processTransaction` is reused
-- | verbatim.
module Snarky.Example.TransactionSnark
  ( Stmt
  , source
  , target
  , baseRule
  , mergeRule
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple, fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Class (class MonadEffect)
import Mina.ChainId (ChainId(..))
import Pickles (StatementIO(..))
import Pickles.Step.Main (RuleOutput)
import Snarky.Circuit.DSL (class CircuitM, AsProverT, F, FVar, Snarky, assertEqual_, exists, true_)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, class TransactionM, getCurrentTransaction, processTransaction)
import Snarky.Example.Types (Account)

type SF = Vesta.ScalarField

-- | A transaction-snark statement: the ledger digest before (`source`)
-- | and after (`target`) the transition. Mina's `Statement` additionally
-- | carries fee_excess / sok_digest / pending_coinbase; this example keeps
-- | just the two ledger hashes.
type Stmt f = Tuple (Digest f) (Digest f)

source :: forall f. Stmt f -> Digest f
source = fst

target :: forall f. Stmt f -> Digest f
target = snd

assertDigestEq
  :: forall t m
   . CircuitM SF (KimchiConstraint SF) t m
  => Digest (FVar SF)
  -> Digest (FVar SF)
  -> Snarky (KimchiConstraint SF) t m Unit
assertDigestEq (Digest a) (Digest b) = assertEqual_ a b

-- | Base "prove-transaction" rule (mpv = 0). The statement's `target` must
-- | be the digest produced by applying the (private) signed transfer to
-- | its `source`. The `SignedTransaction` is conjured via `exists` from
-- | the witness monad's `TransactionM` instance; the prev-states getter is
-- | unused (no previous proofs).
baseRule
  :: forall @d t m
   . Reflectable d Int
  => CircuitM SF (KimchiConstraint SF) t m
  => MonadEffect m
  => AccountMapM m SF d
  => CMT.MerkleRequestM m SF (Account (F SF)) d (Account (FVar SF))
  => TransactionM m SF
  => AsProverT SF m Unit
  -> Stmt (FVar SF)
  -- `prevInput = Stmt` is shared across the program's branches (the merge
  -- branch's prev statements); it is phantom here (0 prevs).
  -> Snarky (KimchiConstraint SF) t m (RuleOutput 0 (Stmt (FVar SF)) Unit)
baseRule _ s = do
  tx <- exists (lift getCurrentTransaction)
  computedTarget <- processTransaction @d Mainnet (source s) tx
  assertDigestEq (target s) computedTarget
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | Merge rule (mpv = 2, Self-recursive). Verifies two proofs of THIS
-- | system and composes them. Needs only the pickles prev-states getter —
-- | no app/ledger advice — so its `m` stays free (an ordinary `StepRule`).
mergeRule
  :: forall t m
   . CircuitM SF (KimchiConstraint SF) t m
  => MonadEffect m
  => AsProverT SF m
       ( StatementIO (Stmt (F SF)) Unit
           /\ StatementIO (Stmt (F SF)) Unit
           /\ Unit
       )
  -> Stmt (FVar SF)
  -> Snarky (KimchiConstraint SF) t m
       (RuleOutput 2 (Stmt (FVar SF)) Unit)
mergeRule getPrevStates s = do
  -- The two sub-statements are the verified prev proofs' public inputs;
  -- witness them from the deferred prev-states getter.
  s1 <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.input
  s2 <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.input
  -- Merge relation (Mina `Merge.main`): the outer statement's source is
  -- s1's source, its target is s2's target, and s1's target connects to
  -- s2's source.
  assertDigestEq (source s) (source s1)
  assertDigestEq (target s) (target s2)
  assertDigestEq (target s1) (source s2)
  pure
    { prevPublicInputs: s1 :< s2 :< Vector.nil
    , proofMustVerify: true_ :< true_ :< Vector.nil
    , publicOutput: unit
    }
