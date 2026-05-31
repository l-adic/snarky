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
  ( Statement(..)
  , baseRule
  , mergeRule
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Class (class MonadEffect)
import Mina.ChainId (ChainId(..))
import Pickles (StatementIO(..))
import Pickles.Step.Main (RuleOutput)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, AsProverT, F, FVar, Snarky, assertEq, check, exists, fieldsToValue, fieldsToVar, sizeInFields, true_, valueToFields, varToFields)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, class TransactionM, getCurrentTransaction, processTransaction)
import Snarky.Example.Types (Account)
import Type.Proxy (Proxy(..))

-- | A transaction-snark statement: the ledger digest before (`source`)
-- | and after (`target`) the transition. Mina's `Statement` additionally
-- | carries fee_excess / sok_digest / pending_coinbase; this example keeps
-- | just the two ledger hashes.
newtype Statement f = Statement
  { source :: Digest f
  , target :: Digest f
  }

-- | `Statement`'s circuit representation is just its two `Digest` fields,
-- | so both instances mediate through the existing `Tuple` instances:
-- | a `Statement` is converted to/from `source /\ target` and the
-- | `(Tuple a b)` `CircuitType`/`CheckedType` instances do the rest
-- | (which in turn delegate to `Digest`'s instances).
instance CircuitType f (Statement (F f)) (Statement (FVar f)) where
  valueToFields (Statement { source, target }) = valueToFields (source /\ target)
  fieldsToValue fields =
    let
      source /\ target = fieldsToValue fields
    in
      Statement { source, target }
  -- `varToFields`/`fieldsToVar` only mention the variable type, so the
  -- Tuple instance's value type must be pinned explicitly (mirrors
  -- `Digest`'s `genericVarToFields @(Digest (F f))`).
  sizeInFields pf _ =
    sizeInFields pf (Proxy :: Proxy (Tuple (Digest (F f)) (Digest (F f))))
  varToFields (Statement { source, target }) =
    varToFields @f @(Tuple (Digest (F f)) (Digest (F f))) (source /\ target)
  fieldsToVar fields =
    let
      source /\ target = fieldsToVar @f @(Tuple (Digest (F f)) (Digest (F f))) fields
    in
      Statement { source, target }

instance CheckedType f c (Statement (FVar f)) where
  check (Statement { source, target }) = check (source /\ target)

-- | Base "prove-transaction" rule (mpv = 0). The statement's `target` must
-- | be the digest produced by applying the (private) signed transfer to
-- | its `source`. The `SignedTransaction` is conjured via `exists` from
-- | the witness monad's `TransactionM` instance; the prev-states getter is
-- | unused (no previous proofs).
baseRule
  :: forall @d t m
   . Reflectable d Int
  => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => MonadEffect m
  => AccountMapM m Vesta.ScalarField d
  => CMT.MerkleRequestM m Vesta.ScalarField (Account (F Vesta.ScalarField)) d (Account (FVar Vesta.ScalarField))
  => TransactionM m Vesta.ScalarField
  => AsProverT Vesta.ScalarField m Unit
  -> Statement (FVar Vesta.ScalarField)
  -- `prevInput = Stmt` is shared across the program's branches (the merge
  -- branch's prev statements); it is phantom here (0 prevs).
  -> Snarky
       (KimchiConstraint Vesta.ScalarField)
       t
       m
       (RuleOutput 0 (Statement (FVar Vesta.ScalarField)) Unit)
baseRule _ (Statement { source, target }) = do
  tx <- exists (lift getCurrentTransaction)
  computedTarget <- processTransaction @d Mainnet source tx
  assertEq target computedTarget
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
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => MonadEffect m
  => AsProverT Vesta.ScalarField m
       ( Tuple2
           (StatementIO (Statement (F Vesta.ScalarField)) Unit)
           (StatementIO (Statement (F Vesta.ScalarField)) Unit)
       )
  -> Statement (FVar Vesta.ScalarField)
  -> Snarky
       (KimchiConstraint Vesta.ScalarField)
       t
       m
       (RuleOutput 2 (Statement (FVar Vesta.ScalarField)) Unit)
mergeRule getPrevStates (Statement { source, target }) = do
  -- The two sub-statements are the verified prev proofs' public inputs;
  -- witness them from the deferred prev-states getter.
  s1@(Statement { source: source1, target: target1 }) <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.input
  s2@(Statement { source: source2, target: target2 }) <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.input
  -- Merge relation (Mina `Merge.main`): the outer statement's source is
  -- s1's source, its target is s2's target, and s1's target connects to
  -- s2's source.
  assertEq source source1
  assertEq target target2
  assertEq target1 source2
  pure
    { prevPublicInputs: s1 :< s2 :< Vector.nil
    , proofMustVerify: true_ :< true_ :< Vector.nil
    , publicOutput: unit
    }
