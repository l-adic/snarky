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

import Data.Reflectable (class Reflectable)
import Pickles.IPA (IpaScalarOps)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, verify)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assert_, const_, false_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)

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
  :: forall nPublic sgOldN t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => Reflectable nPublic Int
  => IpaScalarOps Pallas.ScalarField t m (Type1 (FVar Pallas.ScalarField))
  -> GroupMapParams Pallas.ScalarField
  -> IncrementallyVerifyProofParams nPublic Pallas.ScalarField
  -> Pallas.ScalarField -- ^ claimedDigest: Fq-sponge digest from the Step proof's oracles
  -> IncrementallyVerifyProofInput nPublic sgOldN (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit scalarOps groupMapParams_ params claimedDigest input = do
  success <- evalSpongeM initialSpongeCircuit $
    verify @51 @VestaG scalarOps groupMapParams_ params input false_ (const_ claimedDigest)
  assert_ success
