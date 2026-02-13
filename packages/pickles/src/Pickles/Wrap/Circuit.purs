-- | Wrap circuit: verifies a Step proof via IPA and finalizes deferred values.
-- |
-- | This circuit runs two independent verification steps:
-- | 1. `finalizeOtherProof` — checks deferred values (xi, CIP, b, perm)
-- | 2. `verify` (incrementallyVerifyProof) — checks the IPA opening proof
-- |
-- | The finalize and IVP subcircuits operate on SEPARATE inputs:
-- | - IVP uses the current Step proof's deferred values (cross-field Fp→Fq)
-- | - Finalize uses its own consistently-computed deferred values (same-field Fq)
-- |
-- | The `shouldFinalize` flag enables bootstrapping: dummy proofs use `false`.
-- |
-- | Reference: mina/src/lib/pickles/wrap_main.ml:422-512
module Pickles.Wrap.Circuit
  ( WrapInput
  , WrapParams
  , wrapCircuit
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Pickles.IPA (IpaScalarOps)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, verify)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assert_, const_, false_, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)

-- | Combined input for the Wrap circuit.
-- |
-- | Contains separate inputs for the two independent subcircuits:
-- | - `ivpInput`: commitments, opening proof, and deferred values for IPA verification
-- | - `finalizeInput`: deferred values, witness, and digest for finalize check
type WrapInput nPublic sgOldN fv sf b =
  { ivpInput :: IncrementallyVerifyProofInput nPublic sgOldN fv sf
  , finalizeInput :: FinalizeOtherProofInput fv sf b
  }

-- | Combined parameters for the Wrap circuit.
-- |
-- | Contains both IVP params (curve params, commitments) and
-- | finalize params (domain, endo, linearization).
type WrapParams nPublic f =
  { ivpParams :: IncrementallyVerifyProofParams nPublic f
  , finalizeParams :: FinalizeOtherProofParams f
  }

-- | The Wrap circuit: finalizes deferred values and verifies IPA opening.
-- |
-- | Steps:
-- | 1. Run `finalizeOtherProofCircuit` on the finalize input's deferred values
-- | 2. Assert `finalized || not shouldFinalize`
-- | 3. Run `verify` (incrementallyVerifyProof) on the IVP input's opening proof
-- |
-- | For Wrap, isBaseCase is always false (Wrap always verifies a real Step proof).
-- | The claimedDigest comes from the Step proof's Fq-sponge state.
wrapCircuit
  :: forall nPublic sgOldN t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => Reflectable nPublic Int
  => IpaScalarOps Pallas.ScalarField t m (Type1 (FVar Pallas.ScalarField))
  -> GroupMapParams Pallas.ScalarField
  -> WrapParams nPublic Pallas.ScalarField
  -> Pallas.ScalarField -- ^ claimedDigest: Fq-sponge digest from the Step proof's oracles
  -> WrapInput nPublic sgOldN (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit scalarOps groupMapParams_ params claimedDigest input = do
  -- 1. Finalize deferred values
  { finalized } <- evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit scalarOps params.finalizeParams input.finalizeInput

  -- 2. Assert finalized || not shouldFinalize
  finalizedOrNotRequired <- or_ finalized (not_ input.finalizeInput.unfinalized.shouldFinalize)
  assert_ finalizedOrNotRequired

  -- 3. Verify the Step proof's IPA opening
  success <- evalSpongeM initialSpongeCircuit $
    verify @51 @VestaG scalarOps groupMapParams_ params.ivpParams input.ivpInput false_ (const_ claimedDigest)
  assert_ success
