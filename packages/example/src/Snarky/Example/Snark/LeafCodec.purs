-- | JSON transport for a base proof: serialize a `SerializableCompiledProof`
-- | (the example's `TxnStmt`) so a precompute "server" can ship base proofs
-- | to a browser that reconstructs them and computes only the merge tree.
-- |
-- | Reuses `Pickles.Prove.Codecs.encodeVerifiableProof` for the big wrap-proof
-- | field (nested as a string); the rest of `SerializableCompiledProof` —
-- | `prevEvals` (flat `AllEvals`), the two `messages_for_next_*` vectors, and
-- | the `Statement`'s two ledger digests — serialize through simple-json's
-- | leaf instances.
module Snarky.Example.Snark.LeafCodec
  ( LeafWire
  , encodeLeaf
  , decodeLeaf
  ) where

import Prelude

import Data.Either (Either)
import Data.Newtype (unwrap)
import Data.Vector (Vector)
import Foreign (MultipleErrors)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Codecs (decodeVerifiableProof, encodeVerifiableProof)
import Pickles.Prove.SerializeProof (SerializableCompiledProof)
import Pickles.Types (StatementIO(..), WrapIPARounds)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Example.Transaction.Checked (Statement(..), TxnStmt)

-- | Flat, simple-json-serializable wire form. `verifiable` is the nested
-- | `encodeVerifiableProof` string; `source`/`target` are the statement's two
-- | ledger-digest field values.
type LeafWire =
  { verifiable :: String
  , source :: Vesta.ScalarField
  , target :: Vesta.ScalarField
  , prevEvals :: AllEvals StepField
  , stepChalPolyComms :: Array (AffinePoint StepField)
  , wrapOldBpChals :: Array (Vector WrapIPARounds WrapField)
  }

encodeLeaf :: SerializableCompiledProof TxnStmt -> String
encodeLeaf scp =
  let
    StatementIO { input: Statement { source, target } } = scp.statement
    wire :: LeafWire
    wire =
      { verifiable: encodeVerifiableProof scp.verifiable
      , source: unwrap source
      , target: unwrap target
      , prevEvals: scp.prevEvals
      , stepChalPolyComms: scp.messagesForNextStepProof.challengePolynomialCommitments
      , wrapOldBpChals: scp.messagesForNextWrapProof.oldBulletproofChallenges
      }
  in
    writeJSON wire

decodeLeaf :: String -> Either MultipleErrors (SerializableCompiledProof TxnStmt)
decodeLeaf s = do
  w :: LeafWire <- readJSON s
  verifiable <- decodeVerifiableProof w.verifiable
  pure
    { verifiable
    , statement: StatementIO
        { input: Statement { source: Digest w.source, target: Digest w.target }
        , output: unit
        }
    , prevEvals: w.prevEvals
    , messagesForNextStepProof: { challengePolynomialCommitments: w.stepChalPolyComms }
    , messagesForNextWrapProof: { oldBulletproofChallenges: w.wrapOldBpChals }
    }
