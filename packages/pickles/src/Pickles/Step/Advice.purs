-- | Advisory monad for the Step circuit's private witness data.
-- |
-- | In OCaml Pickles (requests.ml Step module), the Step circuit uses 9
-- | request types. The types and usage are derived from:
-- |   - mina/src/lib/pickles/requests.ml (Step module, lines 120-141)
-- |   - mina/src/lib/pickles/step_main.ml (lines 281-374, exists calls)
-- |   - mina/src/lib/pickles/per_proof_witness.ml (Proof_with_datas type)
-- |
-- | Request inventory:
-- |
-- |   Req.App_state : statement
-- |     The application-specific input (e.g., Schnorr verification data).
-- |     step_main.ml:281: `exists input_typ ~request:(fun () -> Req.App_state)`
-- |
-- |   Req.Compute_prev_proof_parts : previous_proof_statements -> unit Promise.t
-- |     Triggers async pre-computation of previous proof data before the
-- |     prover requests it. step_main.ml:306: async unit request.
-- |
-- |   Req.Proof_with_datas : Per_proof_witness.Constant.No_app_state.t (per proof)
-- |     The main per-proof witness. Contains (per_proof_witness.ml:52-95):
-- |       - wrap_proof: polynomial commitments, evaluations, opening proof
-- |       - proof_state: deferred_values, sponge_digest, messages_for_next_wrap_proof
-- |       - prev_proof_evals: All_evals from the inner step proof
-- |       - prev_challenges: IPA challenges from each previously verified proof
-- |       - prev_challenge_polynomial_commitments: sg points for each previous proof
-- |     step_main.ml:358: `exists ... ~request:(fun () -> Req.Proof_with_datas)`
-- |
-- |   Req.Wrap_index : Plonk_verification_key_evals.t
-- |     Verification key polynomial commitments for the Wrap circuit being verified.
-- |     step_main.ml:354: `exists ... ~request:(fun () -> Req.Wrap_index)`
-- |
-- |   Req.Unfinalized_proofs : (Unfinalized.t, proofs_verified) Vector.t
-- |     Deferred values + shouldFinalize for each previous proof.
-- |     step_main.ml:367: `exists ... ~request:(fun () -> Req.Unfinalized_proofs)`
-- |
-- |   Req.Messages_for_next_wrap_proof : (Digest.t, max_proofs_verified) Vector.t
-- |     Digests for the next Wrap proof (hash of bp challenges + sg).
-- |     step_main.ml:370: `exists ... ~request:(fun () -> Req.Messages_for_next_wrap_proof)`
-- |
-- |   Req.Wrap_domain_indices : (Proofs_verified.t, proofs_verified) Vector.t
-- |     Domain size selection for each wrapped proof.
-- |     step_main.ml:374: `exists ... ~request:(fun () -> Req.Wrap_domain_indices)`
-- |
-- |   Req.Return_value : return_value -> unit
-- |     Prover-side extraction of the application's return value.
-- |     step_main.ml:293: `exists Typ.unit ~request:...`
-- |
-- |   Req.Auxiliary_value : auxiliary_value -> unit
-- |     Prover-side extraction of auxiliary (private) output.
-- |     step_main.ml:298: `exists Typ.unit ~request:...`
-- |
-- | CURRENT STATUS:
-- |   Our getProofWitnesses provides a subset of Proof_with_datas — just the
-- |   polynomial evaluations and domain values needed by finalizeOtherProof.
-- |   The remaining fields (wrap_proof, proof_state, prev_challenges, etc.)
-- |   are not yet part of our circuit.
module Pickles.Step.Advice
  ( class StepWitnessM

  , getProofWitnesses
  , getPrevChallenges
  , getMessages
  , getOpeningProof
  , getFopProofStates
  , getMessagesForNextWrapProof
  , getWrapVerifierIndex
  , getSgOld
  -- Composed advice methods used by Pickles.Step.Main.stepMain.
  -- These mirror OCaml's `Req.App_state`, `Req.Proof_with_datas`,
  -- and `Req.Unfinalized_proofs`.
  , getStepPublicInput
  , getStepPerProofWitnesses
  , getStepUnfinalizedProofs

  -- Parallel v2 class: provides the spec-indexed per-slot carrier.
  -- Sits alongside `StepWitnessM` so callers can migrate one at a time.
  , class StepSlotsM
  , getStepSlotsCarrier
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Step.Prevs (class PrevsCarrier)
import Pickles.Types (PerProofUnfinalized, StepPerProofWitness, VerificationKey)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type1, Type2)

-- | Advisory monad for the Step circuit.
-- |
-- | Parameters:
-- | - `n`: Number of previous proofs being verified (max_proofs_verified)
-- | - `ds`: IPA rounds for the inner Step proof (= StepIPARounds = 16)
-- | - `dw`: IPA rounds for the Wrap proof being verified (= WrapIPARounds = 15)
-- | - `g`: Commitment curve of the Wrap proof being verified (= PallasG for Step)
-- | - `f`: Base field of `g` — uniquely determined via `WeierstrassCurve f g`
-- |        (= Pallas.BaseField = Vesta.ScalarField = StepField)
-- | - `m`: Base monad (Effect for compilation, StepProverM for proving)
-- |
-- | The curve `g` is the primary abstraction: it picks which Wrap proof's
-- | commitments the Step circuit verifies, and determines the circuit's
-- | native field via `WeierstrassCurve f g | g -> f`. Call sites concretize
-- | `g = PallasG` for the Pasta cycle.
class
  ( Monad m
  , WeierstrassCurve f g
  ) <=
  StepWitnessM (n :: Int) (ds :: Int) (dw :: Int) g f m inputVal
  | g -> f
  , m -> inputVal where
  -- | Per-proof polynomial evaluations and domain values for finalizeOtherProof.
  -- | A subset of OCaml's Req.Proof_with_datas (the prev_proof_evals portion).
  getProofWitnesses :: Unit -> m (Vector n (ProofWitness (F f)))

  -- | Expanded bulletproof challenges from each previous proof.
  -- | Used for challenge_digest (OptSponge) and sg_eval (bPoly) computations.
  -- | OCaml: prev_challenges from Req.Proof_with_datas
  getPrevChallenges :: Unit -> m (Vector n (Vector ds (F f)))

  -- | Protocol commitments for IVP verification.
  -- | OCaml: Req.Messages (per previous Wrap proof)
  getMessages
    :: Unit
    -> m
         ( Vector n
             { wComm :: Vector 15 (AffinePoint (F f))
             , zComm :: AffinePoint (F f)
             , tComm :: Vector 7 (AffinePoint (F f))
             }
         )

  -- | Full opening proof for IVP verification.
  -- | OCaml: Req.Openings_proof (per previous Wrap proof)
  -- |
  -- | z1/z2 are returned as Type2-shifted values (cross-field shift for Step).
  -- | The Wrap proof's opening scalars live in Fq (Wrap scalar field), but the
  -- | Step circuit operates in Fp. Type2 encodes the cross-field representation.
  getOpeningProof
    :: Unit
    -> m
         ( Vector n
             { delta :: AffinePoint (F f)
             , sg :: AffinePoint (F f)
             , lr :: Vector dw { l :: AffinePoint (F f), r :: AffinePoint (F f) }
             , z1 :: Type2 (SplitField (F f) Boolean)
             , z2 :: Type2 (SplitField (F f) Boolean)
             }
         )

  -- | FOP proof states (Type1 shifted values) for finalizeOtherProof.
  -- | These come from Per_proof_witness.proof_state (private witness),
  -- | distinct from the public input's Type2(SplitField) unfinalized proofs.
  -- | OCaml: step_main.ml:29 proof_state.deferred_values (Type1)
  getFopProofStates :: Unit -> m (Vector n (UnfinalizedProof ds (F f) (Type1 (F f)) Boolean))

  -- | Digests for the next Wrap proof (one per previous proof).
  -- | In OCaml this is loaded via exists from Req.Messages_for_next_wrap_proof
  -- | (step_main.ml:362-364), NOT computed in-circuit.
  -- | Each digest is a hash of (sg, expanded bp_challenges) for that proof.
  getMessagesForNextWrapProof :: Unit -> m (Vector n (F f))

  -- | Wrap verifier index (VK) as circuit variables.
  -- | In OCaml this enters via exists ~request:(Req.Wrap_index) (step_main.ml:345-348).
  -- | Contains sigma commitments (Vector 7), coefficient commitments (15),
  -- | and index commitments (6). The sigmaLast split (6 + 1) is done at
  -- | use time, not allocation time — OCaml allocates all 7 sigmas together.
  -- |
  -- | Wrapped in `WeierstrassAffinePoint g` so the on-curve checks run during
  -- | `exists`, matching OCaml's `Step_verifier.Inner_curve.typ`.
  getWrapVerifierIndex :: Unit -> m (VerificationKey (WeierstrassAffinePoint g (F f)))

  -- | Per-proof sg points (prev_challenge_polynomial_commitments).
  -- | One point per previous proof, from Per_proof_witness.
  -- | OCaml: per_proof_witness.ml:91 prev_challenge_polynomial_commitments
  getSgOld :: Unit -> m (Vector n (AffinePoint (F f)))

  -- | The rule's public input. For OCaml Input-mode rules this is the
  -- | application-specific `a_var` passed via `exists Req.App_state`
  -- | (step_main.ml:275). For single-field inputs `inputVal = F f`; for
  -- | multi-field inputs `inputVal` is a record/vector of field values.
  -- | The circuit-side `input` var type is paired with `inputVal` through
  -- | the `CircuitType` constraint at the `stepMain` call site.
  getStepPublicInput :: Unit -> m inputVal

  -- | The composed per-proof witness Vector — ONE allocation matching
  -- | OCaml's `exists (Prev_typ.f prev_proof_typs) ~request:Req.Proof_with_datas`.
  -- | Returns a `Vector n` of structured per-proof witnesses; subcircuits
  -- | extract whatever they need via the `StepPerProofWitness` accessors.
  getStepPerProofWitnesses
    :: Unit
    -> m
         ( Vector n
             ( StepPerProofWitness
                 n
                 ds
                 dw
                 (F f)
                 (Type2 (SplitField (F f) Boolean))
                 Boolean
             )
         )

  -- | The composed unfinalized proofs Vector — ONE allocation matching
  -- | OCaml's `exists (Vector.typ' ...) ~request:Req.Unfinalized_proofs`.
  getStepUnfinalizedProofs
    :: Unit
    -> m
         ( Vector n
             ( PerProofUnfinalized
                 dw
                 (Type2 (SplitField (F f) Boolean))
                 (F f)
                 Boolean
             )
         )

-- | Compilation instance: never called, exists only to satisfy the constraint
-- | during `compile` which uses Effect as the base monad.
instance
  ( WeierstrassCurve f g
  , Reflectable n Int
  ) =>
  StepWitnessM n ds dw g f Effect inputVal where
  getProofWitnesses _ = throw "impossible! getProofWitnesses called during compilation"
  getPrevChallenges _ = throw "impossible! getPrevChallenges called during compilation"
  getMessages _ = throw "impossible! getMessages called during compilation"
  getOpeningProof _ = throw "impossible! getOpeningProof called during compilation"
  getFopProofStates _ = throw "impossible! getFopProofStates called during compilation"
  getMessagesForNextWrapProof _ = throw "impossible! getMessagesForNextWrapProof called during compilation"
  getWrapVerifierIndex _ = throw "impossible! getWrapVerifierIndex called during compilation"
  getSgOld _ = throw "impossible! getSgOld called during compilation"
  getStepPublicInput _ = throw "impossible! getStepPublicInput called during compilation"
  getStepPerProofWitnesses _ = throw "impossible! getStepPerProofWitnesses called during compilation"
  getStepUnfinalizedProofs _ = throw "impossible! getStepUnfinalizedProofs called during compilation"

--------------------------------------------------------------------------------
-- Parallel v2 class: spec-indexed per-slot carrier
--
-- Sits alongside `StepWitnessM`. During the migration to spec-indexed
-- per-slot witnesses, callers can depend on this class to obtain the
-- `StepSlot`-tuple carrier (matching OCaml's heterogeneous
-- `H3.T(Per_proof_witness.No_app_state).t`) while still using the
-- existing `StepWitnessM` for the homogeneous methods they haven't
-- migrated yet. Once all callers migrate, `StepWitnessM`'s
-- `getStepPerProofWitnesses` can be dropped.
--------------------------------------------------------------------------------

-- | Produces a spec-indexed nested-tuple carrier where each slot holds
-- | one `StepSlot n_i ds dw …` with its OWN per-slot `n_i`. Matches
-- | OCaml's `exists (Prev_typ.f prev_proof_typs)` — an hlist-typed
-- | allocation per prev, each slot carrying a `Per_proof_witness`
-- | sized by that prev's own `max_proofs_verified`.
-- |
-- | The curve/field type params mirror `StepWitnessM`'s so an instance
-- | can be piggybacked on an existing `StepProverT`-like monad. The
-- | `prevsSpec` / `len` / `carrier` fundep from `PrevsCarrier` pins
-- | the carrier's concrete shape.
class
  ( Monad m
  , WeierstrassCurve f g
  , PrevsCarrier
      prevsSpec
      ds
      dw
      (F f)
      (Type2 (SplitField (F f) Boolean))
      Boolean
      len
      carrier
  ) <=
  StepSlotsM prevsSpec (ds :: Int) (dw :: Int) g f m len carrier
  | g -> f
  , m -> prevsSpec
  , prevsSpec ds dw g f -> len carrier
  where
  getStepSlotsCarrier :: Unit -> m carrier

-- | Compilation instance (Effect) — never actually called; stepMain's
-- | `exists $ lift (getStepSlotsCarrier unit)` discards the AsProverT
-- | body during circuit compilation.
instance
  ( WeierstrassCurve f g
  , PrevsCarrier
      prevsSpec
      ds
      dw
      (F f)
      (Type2 (SplitField (F f) Boolean))
      Boolean
      len
      carrier
  ) =>
  StepSlotsM prevsSpec ds dw g f Effect len carrier where
  getStepSlotsCarrier _ = throw "impossible! getStepSlotsCarrier called during compilation"
