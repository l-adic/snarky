-- | PureScript analog of OCaml `Pickles.Proof.dummy`
-- | (mina/src/lib/crypto/pickles/proof.ml:115-208), specialized to the base
-- | case wrap proof body.
-- |
-- | The OCaml function constructs a compile-time `Proof.t` value with:
-- |
-- | * Commitments: every `w_comm`, `z_comm`, `t_comm` point set to
-- |   `Tock.Curve.(to_affine_exn one)` = the Pallas generator `g0`.
-- | * Opening proof: `lr = [(g0, g0); ...]`, `delta = g0`,
-- |   `challenge_polynomial_commitment = g0`, and `z_1 = Ro.tock ()`,
-- |   `z_2 = Ro.tock ()`.
-- | * Polynomial evaluations: `Dummy.evals.evals.evals` from `dummy.ml`,
-- |   a `Plonk_types.Evals.t` populated with fresh `Ro.tock ()` values.
-- | * `ft_eval1 = Dummy.evals.ft_eval1 = Ro.tock ()`.
-- |
-- | All values are pure data — no cryptography — so the kimchi-level
-- | `ProverProof` the oracle consumes is constructed directly via the
-- | `vestaMakeWireProof` FFI (the PureScript analog of
-- | `Wrap_wire_proof.to_kimchi_proof`).
-- |
-- | The Ro-derived values come from `Pickles.Dummy.roComputeResult`, which
-- | runs the full Ro state machine once and shares the results with the
-- | rest of the dummy machinery so the OCaml global-counter ordering is
-- | preserved exactly.
module Pickles.Proof.Dummy
  ( dummyWrapProof
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (roComputeResult)
import Pickles.ProofFFI (Proof, vestaMakeWireProof)
import Pickles.Types (WrapField)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

-- | The PureScript analog of OCaml `Proof.dummy` (wrap proof body only).
-- |
-- | Only the kimchi `ProverProof`-level part of OCaml `Proof.dummy` is
-- | constructed here: the `messages`, `openings.proof`, `openings.evals`,
-- | and `openings.ft_eval1` fields. OCaml `Proof.dummy` also carries a
-- | `statement` and `prev_evals`, but those are consumed separately by the
-- | step prover (via `expand_proof`) and don't participate in kimchi's
-- | native oracle computation.
-- |
-- | Used by `Pickles.Dummy.dummyStepAdvice` as the "previous wrap proof"
-- | fed to `vestaProofOracles` so the step circuit's in-circuit Fq sponge
-- | squeeze (beta, gamma, alpha, zeta, sponge_digest) matches the advice
-- | values the prover hands it.
dummyWrapProof :: Proof Pallas.G Vesta.BaseField
dummyWrapProof =
  let
    r = roComputeResult

    -- Pallas generator g0 = Tock.Curve.(to_affine_exn one). Pallas points
    -- have coordinates in Pallas.BaseField = Vesta.ScalarField.
    g0 :: AffinePoint Vesta.ScalarField
    g0 = unsafePartial fromJust
      (toAffine (generator :: Pallas.G) :: _ (AffinePoint Vesta.ScalarField))

    g0XY :: Array Vesta.ScalarField
    g0XY = [ g0.x, g0.y ]

    -- w_comm: 15 copies of g0 as (x, y) pairs
    wComm :: Array Vesta.ScalarField
    wComm = Array.concat (Array.replicate 15 g0XY)

    -- z_comm: 1 copy of g0
    zComm :: Array Vesta.ScalarField
    zComm = g0XY

    -- t_comm: 7 copies of g0 (one per quotient-poly chunk)
    tComm :: Array Vesta.ScalarField
    tComm = Array.concat (Array.replicate 7 g0XY)

    -- Opening proof lr: 15 (g0, g0) pairs laid out as l.x,l.y,r.x,r.y
    lr :: Array Vesta.ScalarField
    lr = Array.concat (Array.replicate 15 (g0XY <> g0XY))

    delta :: Array Vesta.ScalarField
    delta = g0XY

    sg :: Array Vesta.ScalarField
    sg = g0XY

    -- Evaluations: flatten `roComputeResult.wrapDummyEvals` into the kimchi
    -- eval order, matching OCaml `wrap_wire_proof.ml` Evaluations.to_kimchi
    -- (wrap_wire_proof.ml:107-134). The ordering is:
    --
    --   witness (w)[0..14] | coefficients[0..14] | z | sigma (s)[0..5]
    --   | generic | poseidon | complete_add | mul | emul | endomul_scalar
    --
    -- `wrapDummyEvals.indexEvals` holds the 6 selectors in the exact order
    -- `[generic, poseidon, completeAdd, mul, emul, endomulScalar]` (matches
    -- `Pickles.Dummy.roComputeResult`).
    evals = wrapDummyEvals

    flattenVec :: forall n. Vector n { zeta :: WrapField, omegaTimesZeta :: WrapField } -> Array WrapField
    flattenVec v =
      Array.concatMap (\pe -> [ pe.zeta, pe.omegaTimesZeta ])
        (Vector.toUnfoldable v)

    flattenPe :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> Array WrapField
    flattenPe pe = [ pe.zeta, pe.omegaTimesZeta ]

    evalsFlat :: Array WrapField
    evalsFlat =
      flattenVec evals.witnessEvals
        <> flattenVec evals.coeffEvals
        <> flattenPe evals.zEvals
        <> flattenVec evals.sigmaEvals
        <> flattenVec evals.indexEvals

    wrapDummyEvals = r.wrapDummyEvals
  in
    vestaMakeWireProof
      { wComm
      , zComm
      , tComm
      , lr
      , delta
      , sg
      , z1: r.proofZ1
      , z2: r.proofZ2
      , evals: evalsFlat
      , ftEval1: evals.ftEval1
      }
