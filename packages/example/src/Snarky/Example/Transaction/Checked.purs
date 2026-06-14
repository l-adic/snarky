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
-- | `AccountMapM`, `TransferM`) inside a pickles rule. Because pickles
-- | now runs rules in the caller's bare monad `m`, those are ordinary
-- | constraints on `m`, discharged at the concrete app monad when the
-- | entry is built (`mkRuleEntry @AppM`). `processTransaction` is reused
-- | verbatim.
module Snarky.Example.Transaction.Checked
  ( Statement(..)
  , baseRule
  , mergeRule
  , applyTxChecked
  , compileTxCircuit
  , TxnStmt
  , BaseProverInput
  , MergeProverInput
  , CompiledTx
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (toHashInput)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr (Signature(..)) as Schnorr
import Data.Tuple (Tuple, fst, snd)
import Data.Tuple.Nested (type (/\), Tuple2, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Mina.ChainId (ChainId, signaturePrefix)
import Pickles (BranchProver(..), Compiled, CompiledProof, PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), Slots2, StatementIO(..), Verifier, compileMulti, mkRuleEntry)
import Pickles.Step.Main (RuleOutput)
import Snarky.Backend.Advice (badAdvice)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, AsProver, FVar, Snarky, add_, assertEq, assert_, check, const_, exists, fieldsToValue, fieldsToVar, liftAdvice, not_, read, sizeInFields, true_, unpack_, valueToFields, varToFields)
import Snarky.Circuit.MerkleTree (MERKLE)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Schnorr (Signature(..), verifies)
import Snarky.Circuit.Schnorr.Shifted as Shifted
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask, emptyMask)
import Snarky.Example.Transaction.Monad (ACCOUNT_MAP, TRANSACTION, getAccountId, getCurrentTransaction, runTransferMaskM)
import Snarky.Example.Transaction.Types (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types (Account(..), PublicKey(..), addWithOverflow, subWithUnderflow)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

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
instance CircuitType f (Statement f) (Statement (FVar f)) where
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
    sizeInFields pf (Proxy :: Proxy (Tuple (Digest f) (Digest f)))
  varToFields (Statement { source, target }) =
    varToFields @f @(Tuple (Digest f) (Digest f)) (source /\ target)
  fieldsToVar fields =
    let
      source /\ target = fieldsToVar @f @(Tuple (Digest f) (Digest f)) fields
    in
      Statement { source, target }

instance CheckedType f c (Statement (FVar f)) where
  check (Statement { source, target }) = check (source /\ target)

-- | Base "prove-transaction" rule (mpv = 0). The statement's `target` must
-- | be the digest produced by applying the (private) signed transfer to
-- | its `source`. The `SignedTransaction` is conjured via `exists` from
-- | the witness monad's `TransferM` instance; the prev-states getter is
-- | unused (no previous proofs).
baseRule
  :: forall @d r
   . Reflectable d Int
  => ChainId
  -> AsProver Vesta.ScalarField (TxAdviceRow d r) Unit
  -> Statement (FVar Vesta.ScalarField)
  -- `prevInput = Stmt` is shared across the program's branches (the merge
  -- branch's prev statements); it is phantom here (0 prevs).
  -> Snarky
       Vesta.ScalarField
       (KimchiConstraint Vesta.ScalarField)
       (TxAdviceRow d r)
       (RuleOutput 0 (Statement (FVar Vesta.ScalarField)) Unit)
baseRule chainId _ (Statement { source, target }) = do
  tx <- exists (liftAdvice getCurrentTransaction)
  computedTarget <- applyTxChecked @d chainId source tx
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
  :: forall r
   . AsProver Vesta.ScalarField r
       ( Tuple2
           (StatementIO (Statement Vesta.ScalarField) Unit)
           (StatementIO (Statement Vesta.ScalarField) Unit)
       )
  -> Statement (FVar Vesta.ScalarField)
  -> Snarky
       Vesta.ScalarField
       (KimchiConstraint Vesta.ScalarField)
       r
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

--------------------------------------------------------------------------------

-- | Transfer tokens between accounts.
-- |
-- | This circuit:
-- | 1. Takes a transaction (public keys + amount)
-- | 2. Looks up addresses from public keys via AccountMapM
-- | 3. Fetches sender account, verifies ownership, debits the amount
-- | 4. Fetches receiver account, verifies ownership, credits the amount
-- | 5. Returns the new merkle root
-- |
-- | Note: Addresses are assigned sequentially in Mina (not derived from public keys).
-- | The circuit verifies the account at each address has the expected public key.
-- | The open advice row the transfer circuits request from (close it with
-- | `r := ()` to get `Monad.TransferAdvice`, the row the handlers serve).
type TxAdviceRow d r =
  MERKLE Vesta.ScalarField (Account Vesta.ScalarField) d
    + ACCOUNT_MAP d
    + TRANSACTION
    + r

applyTxChecked
  :: forall @d r
   . Reflectable d Int
  => ChainId
  -> Digest (FVar Vesta.ScalarField)
  -> SignedTransaction (FVar Vesta.ScalarField)
  -> Snarky Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) (TxAdviceRow d r) (Digest (FVar Vesta.ScalarField))
applyTxChecked chainId root (SignedTransaction { signature, transaction }) = do
  let
    Transaction { nonce, transfer: Transfer { from, to, amount } } = transaction
    Schnorr.Signature { r, s } = signature
  -- Verify the sender's signature over the transaction in-circuit. The
  -- pure signature carries `s` as a field; unpack it into the 255-bit
  -- form the circuit verifier consumes.

  signatureVerifies <- do
    sBits <- unpack_ s (Proxy @255)
    scalarOps <- Shifted.pallasScalarOps
    verifies (signaturePrefix chainId) scalarOps
      { publicKey: un PublicKey from
      , signature: Signature { r, s: sBits }
      , message: toHashInput transaction
      }
  assert_ signatureVerifies

  -- Debit sender: verify ownership and subtract amount
  { root: root' } <- do
    fromAddr <- exists do
      fromPk <- read from
      liftAdvice $ getAccountId fromPk
    CMT.fetchAndUpdate @(Account Vesta.ScalarField) fromAddr root \(Account acc) -> do
      -- Verify sender owns this account
      assertEq acc.publicKey from
      assertEq acc.nonce nonce
      -- Debit the amount
      { result: newBalance, underflow } <- acc.tokenBalance `subWithUnderflow` amount
      assert_ (not_ underflow)
      pure $ Account acc { tokenBalance = newBalance, nonce = add_ nonce (const_ one) }

  -- Credit receiver: verify ownership and add amount
  { root: root'' } <- do
    toAddr <- exists do
      toPk <- read to
      liftAdvice $ getAccountId toPk

    CMT.fetchAndUpdate @(Account Vesta.ScalarField) toAddr root' \(Account acc) -> do
      -- Verify receiver owns this account
      assertEq acc.publicKey to
      -- Credit the amount
      { result: newBalance, overflow } <- acc.tokenBalance `addWithOverflow` amount
      assert_ (not_ overflow)
      pure $ Account acc { tokenBalance = newBalance }

  pure root''

type TxnStmt = StatementIO (Statement Vesta.ScalarField) Unit

-- | The two-branch program. Branch 0 (base) has no prev slots; branch 1
-- | (merge) has two `Self` slots, each width 2 (a proof of THIS mpv=2
-- | program) at one chunk.
type TxnSnarkRules =
  RulesCons 0 Unit Unit Unit
    ( RulesCons 2
        (TxnStmt /\ TxnStmt /\ Unit)
        (Slot Compiled 2 1 TxnStmt /\ Slot Compiled 2 1 TxnStmt /\ Unit)
        (SlotWrapKey /\ SlotWrapKey /\ Unit)
        RulesNil
    )

type BaseProverInput d =
  { env :: { mask :: Mask d, tx :: SignedTransaction Vesta.ScalarField }
  , statement :: Statement Vesta.ScalarField
  }

type MergeProverInput =
  { proof1 :: CompiledProof 2 TxnStmt
  , proof2 :: CompiledProof 2 TxnStmt
  , statement :: Statement Vesta.ScalarField
  }

type CompiledTx d =
  { baseProver :: BaseProverInput d -> Effect (CompiledProof 2 TxnStmt)
  , mergeProver :: MergeProverInput -> Effect (CompiledProof 2 TxnStmt)
  , verifier :: Verifier
  }

compileTxCircuit
  :: forall d
   . Reflectable d Int
  => ChainId
  -> { vestaSrs :: CRS VestaG
     , pallasSrs :: CRS PallasG
     }
  -> Effect (CompiledTx d)
compileTxCircuit chainId srs = do
  let
    cfg =
      { srs
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: Nothing
      }
  baseEntry <-
    mkRuleEntry
      @2
      @Unit
      @(Statement Vesta.ScalarField)
      @1
      @1
      @(TxAdviceRow d ())
      (baseRule @d chainId)
      unit
  mergeEntry <-
    mkRuleEntry
      @2
      @Unit
      @(Statement Vesta.ScalarField)
      @1
      @1
      @(TxAdviceRow d ())
      mergeRule
      (tuple2 Self Self)

  let rules = tuple2 baseEntry mergeEntry

  out <-
    compileMulti
      @TxnSnarkRules
      @Unit
      @(Statement Vesta.ScalarField)
      @(Slots2 2 2)
      @1
      badAdvice
      cfg
      rules
  let
    BranchProver baseProver = fst out.provers
    BranchProver mergeProver = fst (snd out.provers)
  pure
    { baseProver: \{ env, statement } -> do
        mask <- Ref.new env.mask
        baseProver (runTransferMaskM { currentTransaction: Just env.tx, mask })
          { appInput: statement
          , prevs: unit
          , sideloadedVKs: unit
          } >>= case _ of
          Left err -> throw $ show err
          Right res -> pure res
    , mergeProver: \{ statement, proof1, proof2 } -> do
        mask <- Ref.new emptyMask
        mergeProver (runTransferMaskM { currentTransaction: Nothing, mask })
          { appInput: statement
          , prevs: tuple2 (InductivePrev proof1 out.tag) (InductivePrev proof2 out.tag)
          , sideloadedVKs: tuple2 unit unit
          } >>= case _ of
          Left err -> throw $ show err
          Right res -> pure res
    , verifier: out.verifier
    }

