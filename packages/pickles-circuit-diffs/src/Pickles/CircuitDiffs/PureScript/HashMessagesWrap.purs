module Pickles.CircuitDiffs.PureScript.HashMessagesWrap
  ( compileHashMessagesWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (WrapIPARounds)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Types (Field)
import RandomOracle.Sponge (Sponge) as RO
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEq)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

-- | hash_messages_for_next_wrap_proof circuit.
-- |
-- | Input layout (33 fields), matching MaxProofsVerified = 2:
-- |   0-14:  expanded bp challenges vector 0 (WrapIPARounds = 15)
-- |   15-29: expanded bp challenges vector 1 (WrapIPARounds = 15)
-- |   30-31: sg (x, y)
-- |   32:    claimed_digest
-- |
-- | Reference: mina/src/lib/pickles/wrap_hack.ml:119-142
hashMessagesWrapCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => Vector 33 (FVar Field)
  -> Snarky (KimchiConstraint Field) t m Unit
hashMessagesWrapCircuit inputs = do
  let
    at = unsafeIdx inputs

    chals0 :: Vector WrapIPARounds (FVar Field)
    chals0 = Vector.generate \j -> at (getFinite j)

    chals1 :: Vector WrapIPARounds (FVar Field)
    chals1 = Vector.generate \j -> at (15 + getFinite j)

    sg = { x: at 30, y: at 31 }
    claimed = at 32

  digest <- evalSpongeM (initialSpongeCircuit :: RO.Sponge (FVar Field)) $
    hashMessagesForNextWrapProofCircuit'
      { sg
      , allChallenges: chals0 :< chals1 :< Vector.nil
      }

  assertEq digest claimed

compileHashMessagesWrap :: CompiledCircuit Field
compileHashMessagesWrap =
  compilePure (Proxy @(Vector 33 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> hashMessagesWrapCircuit inputs)
    Kimchi.initialState
