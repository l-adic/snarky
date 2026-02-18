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
  , StepPublicInput
  , WrapParams
  , wrapCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Pickles.IPA (IpaScalarOps)
import Pickles.PublicInputCommit (class PublicInputCommit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Types (StepStatement)
import Pickles.Verify (IncrementallyVerifyProofParams, verify)
import Pickles.Wrap.Advice (class WrapWitnessM, getDeferredValues, getEvals, getMessages, getOpeningProof, getPrevChallengeDigest, getUnfinalizedProof)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assert_, const_, exists, false_, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)

-- | Public input for the Wrap circuit.
-- |
-- | Currently Unit — the Wrap circuit has no public inputs.
-- | In OCaml Pickles, the Wrap's public input is a WrapStatement (~29 fields:
-- | deferred values + message digests). That will be added when hash stubs
-- | are implemented. For now, all data enters privately via WrapWitnessM.
type WrapInput = Unit

-- | The Step proof's public input type as seen by the Wrap verifier for x_hat.
-- |
-- | In OCaml, the Step circuit's public input is Step.Statement (not the full
-- | Step I/O). The Step circuit obtains its input (app_state, unfinalized_proofs)
-- | as private witness via Req.App_state, and the public input contains only
-- | the StepStatement (unfinalized proofs, message digests).
-- |
-- | This type is the StepStatement parameterized with Type2 shifted scalars
-- | (cross-field Fp→Fq representation), matching how the Step proof's deferred
-- | values are encoded in the public input.
-- |
-- | Parameterized by `fv` and `b` so the same alias works at both
-- | value level (F f, Boolean) and variable level (FVar f, BoolVar f).
type StepPublicInput :: Int -> Int -> Int -> Type -> Type -> Type
type StepPublicInput n ds dw fv b =
  StepStatement n ds dw fv (Type2 fv b) b

-- | Combined parameters for the Wrap circuit.
-- |
-- | Contains both IVP params (curve params, commitments) and
-- | finalize params (domain, endo, linearization).
type WrapParams f =
  { ivpParams :: IncrementallyVerifyProofParams f
  , finalizeParams :: FinalizeOtherProofParams f
  }

-- | The Wrap circuit: finalizes deferred values and verifies IPA opening.
-- |
-- | Steps:
-- | 1. Obtain all private witness data via advisory monad
-- | 2. Run `finalizeOtherProofCircuit` on the finalize input's deferred values
-- | 3. Assert `finalized || not shouldFinalize`
-- | 4. Run `verify` (incrementallyVerifyProof) on the IVP input's opening proof
-- |
-- | For Wrap, isBaseCase is always false (Wrap always verifies a real Step proof).
-- | The claimedDigest comes from the Step proof's Fq-sponge state.
-- |
-- | All data enters as private witness via WrapWitnessM. The circuit has no
-- | public inputs (WrapInput = Unit).
-- |
-- | The `existsStepStatement` parameter is an allocation action that creates
-- | circuit variables for the Step proof's public input (StepStatement).
-- | It's constructed at the call site (where concrete types are known) using
-- | `exists` with the advisory monad.
-- |
-- | In OCaml, the Wrap circuit's x_hat (publicInputCommit) is computed over
-- | the packed Step.Statement, NOT the full Step I/O. By passing only
-- | StepStatement to `verify`, we match OCaml's approach and avoid the
-- | expensive MSM over the full ~77 field Step I/O.
wrapCircuit
  :: forall n @ds dw _l3 t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => WrapWitnessM ds m Pallas.ScalarField
  => Reflectable ds Int
  => Reflectable dw Int
  => Reflectable n Int
  => Add 1 _l3 ds
  => PublicInputCommit
       (StepPublicInput n ds dw (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField))
       Pallas.ScalarField
  => IpaScalarOps Pallas.ScalarField t m (Type1 (FVar Pallas.ScalarField))
  -> GroupMapParams Pallas.ScalarField
  -> WrapParams Pallas.ScalarField
  -> Pallas.ScalarField -- ^ claimedDigest: Fq-sponge digest from the Step proof's oracles
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m
       (StepPublicInput n ds dw (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField))
  -> WrapInput
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit scalarOps groupMapParams_ params claimedDigest existsStepStatement _ = do
  -- 1. Obtain private witness data via advisory monad
  -- Step statement obtained privately (OCaml: pack_statement prev_statement)
  publicInput <- existsStepStatement
  witness <- exists $ lift $ getEvals @ds unit
  messages <- exists $ lift $ getMessages @ds unit
  openingProof <- exists $ lift $ getOpeningProof @ds unit
  deferredValues <- exists $ lift $ getDeferredValues @ds unit
  unfinalized <- exists $ lift $ getUnfinalizedProof @ds unit
  prevChallengeDigest <- exists $ lift $ getPrevChallengeDigest @ds unit

  -- 2. Finalize deferred values
  { finalized } <- evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit scalarOps params.finalizeParams
      { unfinalized, witness, prevChallengeDigest }

  -- 3. Assert finalized || not shouldFinalize
  finalizedOrNotRequired <- or_ finalized (not_ unfinalized.shouldFinalize)
  assert_ finalizedOrNotRequired

  -- 4. Verify the Step proof's IPA opening
  let
    fullIvpInput =
      { publicInput
      , sgOld: Vector.nil
      , deferredValues
      , wComm: messages.wComm
      , zComm: messages.zComm
      , tComm: messages.tComm
      , opening: openingProof
      }
  success <- evalSpongeM initialSpongeCircuit $
    verify @VestaG scalarOps groupMapParams_ params.ivpParams fullIvpInput false_ (const_ claimedDigest)
  assert_ success
