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
  , WrapInputVar
  , StepPublicInput
  , WrapParams
  , wrapCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Dummy (dummyWrapChallengesExpanded)
import Pickles.IPA (IpaScalarOps)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Types (StepStatement, WrapIPARounds, WrapStatement)
import Pickles.Verify (verify)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOpeningProof, getPrevChallengeDigest, getStepIOFields, getUnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofCircuit)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assert_, equals_, exists, false_, fieldsToValue, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams, Type1, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-- | Public input for the Wrap circuit (value level).
-- |
-- | In OCaml Pickles, the Wrap circuit receives ~29 fields as public input:
-- | deferred values, sponge digest, and message digests. The next Step circuit
-- | verifies these when checking the Wrap proof.
-- |
-- | Parameterized by `ds` (Step IPA rounds) which determines the size of
-- | bulletproof challenges in the deferred values.
-- |
-- | Use with `Proxy @(WrapInput ds)` in `compile`. The circuit function
-- | receives `WrapInputVar ds` (variable-level version) via `CircuitType`.
type WrapInput :: Int -> Type
type WrapInput ds = WrapStatement ds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))

-- | Public input for the Wrap circuit (variable level).
-- |
-- | This is what the circuit function actually receives after `compile`
-- | maps the value-level `WrapInput ds` through `CircuitType`.
type WrapInputVar :: Int -> Type
type WrapInputVar ds = WrapStatement ds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))

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
-- | Flat record containing all fields needed by both subcircuits:
-- | - IVP: curveParams, lagrangeComms, blindingH, sigmaCommLast, columnComms, indexDigest, groupMapParams
-- | - Finalize: domain, domainLog2, zkRows, linearizationPoly
-- | - Shared: endo
-- |
-- | Row-polymorphic functions accept this as a superset of their required fields.
type WrapParams :: Type -> Type
type WrapParams f =
  { -- IVP params
    curveParams :: CurveParams f
  , lagrangeComms :: Array (AffinePoint (F f))
  , blindingH :: AffinePoint (F f)
  , sigmaCommLast :: AffinePoint (F f)
  , columnComms ::
      { index :: Vector 6 (AffinePoint (F f))
      , coeff :: Vector 15 (AffinePoint (F f))
      , sigma :: Vector 6 (AffinePoint (F f))
      }
  , indexDigest :: f
  , groupMapParams :: GroupMapParams f
  -- Finalize params
  , domain :: { generator :: f, shifts :: Vector 7 f }
  , domainLog2 :: Int
  , zkRows :: Int
  , linearizationPoly :: LinearizationPoly f
  -- Shared
  , endo :: f
  }

-- | The Wrap circuit: finalizes deferred values and verifies IPA opening.
-- |
-- | Steps:
-- | 1. Obtain private witness data via advisory monad
-- | 2. Run `finalizeOtherProofCircuit` on the public input's deferred values
-- | 3. Assert `finalized || not shouldFinalize`
-- | 4. Run `verify` (incrementallyVerifyProof) on the IVP input's opening proof
-- |
-- | For Wrap, isBaseCase is always false (Wrap always verifies a real Step proof).
-- | The claimedDigest comes from the WrapStatement public input.
-- |
-- | The WrapStatement public input provides Fp-origin deferred values for IVP.
-- | The finalize subcircuit uses separate Fq-recomputed deferred values from
-- | the private witness (getUnfinalizedProof). These are about different proofs:
-- | IVP verifies the current Step proof, finalize checks previous Wrap proofs.
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
  :: forall @n @ds _l3 t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => WrapWitnessM ds WrapIPARounds m Pallas.ScalarField
  => Reflectable ds Int
  => Reflectable n Int
  => Add 1 _l3 ds
  => IpaScalarOps Pallas.ScalarField t m (Type1 (FVar Pallas.ScalarField))
  -> WrapParams Pallas.ScalarField
  -> WrapInputVar ds
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit scalarOps params wrapStmt = do
  -- 1. Obtain private witness data via advisory monad
  -- Step statement obtained privately (OCaml: pack_statement prev_statement)
  publicInput <- exists $ lift $ do
    fs <- getStepIOFields @ds @WrapIPARounds @m @Pallas.ScalarField unit
    pure $ fieldsToValue @_ @(StepPublicInput n ds WrapIPARounds (F Pallas.ScalarField) Boolean) (map unwrap fs)
  witness <- exists $ lift $ getEvals @ds @WrapIPARounds unit
  messages <- exists $ lift $ getMessages @ds @WrapIPARounds unit
  openingProof <- exists $ lift $ getOpeningProof @ds @WrapIPARounds unit
  -- Unfinalized proof for finalize (private witness, Fq-recomputed deferred values).
  -- Distinct from WrapStatement's Fp-origin deferred values used by IVP.
  -- OCaml: prev_proof_state.unfinalized_proofs
  unfinalized <- exists $ lift $ getUnfinalizedProof @ds @WrapIPARounds @_ @Pallas.ScalarField unit
  prevChallengeDigest <- exists $ lift $ getPrevChallengeDigest @ds @WrapIPARounds unit

  -- 2. Finalize deferred values (uses private unfinalized proof)
  { finalized, expandedChallenges } <- evalSpongeM initialSpongeCircuit $
    finalizeOtherProofCircuit scalarOps params
      { unfinalized, witness, prevChallengeDigest }

  -- 3. Assert finalized || not shouldFinalize
  finalizedOrNotRequired <- or_ finalized (not_ unfinalized.shouldFinalize)
  assert_ finalizedOrNotRequired

  -- 4. Verify the Step proof's IPA opening (uses public input deferred values)
  let
    fullIvpInput =
      { publicInput
      , sgOld: Vector.nil
      , deferredValues: wrapStmt.proofState.deferredValues
      , wComm: messages.wComm
      , zComm: messages.zComm
      , tComm: messages.tComm
      , opening: openingProof
      }
  success <- evalSpongeM initialSpongeCircuit $
    verify @VestaG scalarOps params fullIvpInput false_
      wrapStmt.proofState.spongeDigestBeforeEvaluations
  assert_ success

  -- 5. Compute and assert messagesForNextWrapProof hash
  computedDigest <- evalSpongeM initialSpongeCircuit $
    hashMessagesForNextWrapProofCircuit
      { sg: openingProof.sg
      , expandedChallenges
      , dummyChallenges: dummyWrapChallengesExpanded
      }
  assert_ =<< equals_ computedDigest wrapStmt.proofState.messagesForNextWrapProof
