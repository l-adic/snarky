-- | Wrap circuit: verifies a Step proof via IPA.
-- |
-- | This is the "inner" Wrap circuit that runs incrementallyVerifyProof
-- | on a Step proof. For the base Wrap case (no previous Wrap proofs
-- | to finalize), this is the entire circuit.
-- |
-- | Generic over field f and curve g — works for both Wrap (Fq, VestaG)
-- | and could be reused by Step (Fp, PallasG).
module Pickles.Wrap.Circuit
  ( wrapCircuit
  ) where

import Prelude

import Data.Identity (Identity)
import Data.Reflectable (class Reflectable)
import Pickles.IPA (IpaScalarOps)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)

-- | The Wrap circuit: verifies a Step proof via IPA.
-- |
-- | Runs incrementallyVerifyProof and asserts the result is successful.
-- | All fields in the input are private witness data.
wrapCircuit
  :: forall @nChunks nPublic sgOldN f f' @g sf t bitsUsed sDiv2Bits _l _l2
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => PoseidonField f
  => HasEndo f f'
  => HasSqrt f
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t Identity
  => Add bitsUsed _l 255
  => Add sDiv2Bits 1 255
  => Mul 5 nChunks bitsUsed
  => Reflectable sDiv2Bits Int
  => Reflectable bitsUsed Int
  => Reflectable nPublic Int
  => Add 1 _l2 7
  => IpaScalarOps f t Identity sf
  -> GroupMapParams f
  -> IncrementallyVerifyProofParams nPublic f
  -> IncrementallyVerifyProofInput nPublic sgOldN (FVar f) sf
  -> Snarky (KimchiConstraint f) t Identity Unit
wrapCircuit scalarOps groupMapParams_ params input = do
  { success } <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @nChunks @g scalarOps groupMapParams_ params input
  assert_ success
