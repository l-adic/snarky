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
-- | Private witness data (polynomial evaluations for finalize) is obtained
-- | via the WrapWitnessM advisory monad, not passed as public input.
-- |
-- | Reference: mina/src/lib/pickles/wrap_main.ml:422-512
module Pickles.Wrap.Circuit
  ( WrapInput
  , WrapParams
  , wrapCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Pickles.IPA (IpaScalarOps)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Verify (IncrementallyVerifyProofParams, verify)
import Pickles.Verify.Types (DeferredValues, UnfinalizedProof)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOpeningProof)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assert_, const_, exists, false_, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Combined input for the Wrap circuit.
-- |
-- | Contains public inputs for the two independent subcircuits:
-- | - `ivpInput`: deferred values and opening proof for IPA verification
-- |     (commitments wComm/zComm/tComm are obtained privately via WrapWitnessM.getMessages)
-- | - `finalizeInput`: unfinalized proof and digest for finalize check
-- |     (witness data is obtained privately via WrapWitnessM.getEvals)
-- |
-- | Both subcircuits verify the Step proof, so both use `ds` (Step IPA rounds).
-- | `dw` is phantom here (will be needed for sgOld/old Wrap proof challenges).
type WrapInput :: Int -> Int -> Int -> Int -> Type -> Type -> Type -> Type
type WrapInput nPublic sgOldN ds dw fv sf b =
  { ivpInput ::
      { publicInput :: Vector nPublic fv
      , sgOld :: Vector sgOldN (AffinePoint fv)
      , deferredValues :: DeferredValues ds fv sf
      }
  , finalizeInput ::
      { unfinalized :: UnfinalizedProof ds fv sf b
      , prevChallengeDigest :: fv
      }
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
-- | 1. Obtain polynomial evaluations privately via advisory monad
-- | 2. Run `finalizeOtherProofCircuit` on the finalize input's deferred values
-- | 3. Assert `finalized || not shouldFinalize`
-- | 4. Run `verify` (incrementallyVerifyProof) on the IVP input's opening proof
-- |
-- | For Wrap, isBaseCase is always false (Wrap always verifies a real Step proof).
-- | The claimedDigest comes from the Step proof's Fq-sponge state.
wrapCircuit
  :: forall nPublic sgOldN ds dw _l3 t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => WrapWitnessM ds m Pallas.ScalarField
  => Reflectable nPublic Int
  => Reflectable ds Int
  => Add 1 _l3 ds
  => IpaScalarOps Pallas.ScalarField t m (Type1 (FVar Pallas.ScalarField))
  -> GroupMapParams Pallas.ScalarField
  -> WrapParams nPublic Pallas.ScalarField
  -> Pallas.ScalarField -- ^ claimedDigest: Fq-sponge digest from the Step proof's oracles
  -> WrapInput nPublic sgOldN ds dw (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit scalarOps groupMapParams_ params claimedDigest input = do
  -- 1. Obtain private witness data (polynomial evaluations)
  witness <- exists $ lift $ getEvals @ds unit

  -- 2. Obtain private protocol commitments
  messages <- exists $ lift $ getMessages @ds unit

  -- 3. Obtain private opening proof
  openingProof <- exists $ lift $ getOpeningProof @ds unit

  -- 4. Finalize deferred values
  { finalized } <- evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit scalarOps params.finalizeParams
      { unfinalized: input.finalizeInput.unfinalized
      , witness
      , prevChallengeDigest: input.finalizeInput.prevChallengeDigest
      }

  -- 5. Assert finalized || not shouldFinalize
  finalizedOrNotRequired <- or_ finalized (not_ input.finalizeInput.unfinalized.shouldFinalize)
  assert_ finalizedOrNotRequired

  -- 6. Verify the Step proof's IPA opening
  --    Reconstruct full IVP input from public parts + private witness data
  let
    fullIvpInput =
      { publicInput: input.ivpInput.publicInput
      , sgOld: input.ivpInput.sgOld
      , deferredValues: input.ivpInput.deferredValues
      , wComm: messages.wComm
      , zComm: messages.zComm
      , tComm: messages.tComm
      , opening: openingProof
      }
  success <- evalSpongeM initialSpongeCircuit $
    verify @51 @VestaG scalarOps groupMapParams_ params.ivpParams fullIvpInput false_ (const_ claimedDigest)
  assert_ success
