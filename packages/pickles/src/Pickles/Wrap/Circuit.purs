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
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, verify)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assert_, const_, false_)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve)

-- | The Wrap circuit: verifies a Step proof via IPA.
-- |
-- | Runs `verify` which calls incrementallyVerifyProof and additionally asserts:
-- |   1. Sponge digest matches the claimed value from the Step proof
-- |   2. Bulletproof challenges match (bypassed for base case)
-- |
-- | For Wrap, isBaseCase is always false (Wrap always verifies a real Step proof).
-- | The claimedDigest comes from the Step proof's Fq-sponge state.
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
  -> f -- ^ claimedDigest: Fq-sponge digest from the Step proof's oracles
  -> IncrementallyVerifyProofInput nPublic sgOldN (FVar f) sf
  -> Snarky (KimchiConstraint f) t Identity Unit
wrapCircuit scalarOps groupMapParams_ params claimedDigest input = do
  success <- evalSpongeM initialSpongeCircuit $
    verify @nChunks @g scalarOps groupMapParams_ params input false_ (const_ claimedDigest)
  assert_ success
