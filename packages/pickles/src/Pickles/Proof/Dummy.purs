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
-- | Ro-derived values come from the caller-supplied `BaseCaseDummies`
-- | so the circuit's compile-derived Ro state is the single source of truth.
module Pickles.Proof.Dummy
  ( dummyWrapProof
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Field (WrapField)
import Pickles.ProofFFI (Proof, vestaMakeWireProof)
import Pickles.Step.Dummy (BaseCaseDummies)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Build the kimchi-level wrap proof body from a `BaseCaseDummies`.
-- | Consumes `bcd.proofDummy.{z1, z2}` and `bcd.dummyEvals` — the exact
-- | shape OCaml's `Proof.dummy` produces, threaded in from the circuit's
-- | `computeBaseCaseDummies` output.
dummyWrapProof
  :: BaseCaseDummies
  -> Proof Pallas.G Vesta.BaseField
dummyWrapProof bcd =
  let
    prf = bcd.proofDummy
    evals = bcd.dummyEvals

    -- Pallas generator g0 = Tock.Curve.(to_affine_exn one). Pallas points
    -- have coordinates in Pallas.BaseField = Vesta.ScalarField.
    -- Generator is never the point-at-infinity, so `toAffine` is always `Just`.
    g0 = unsafePartial $ fromJust (toAffine (generator :: Pallas.G))

    g0XY = [ g0.x, g0.y ]

    -- w_comm: 15 copies of g0 as (x, y) pairs
    wComm = Array.concat (Array.replicate 15 g0XY)

    -- z_comm: 1 copy of g0
    zComm = g0XY

    -- t_comm: 7 copies of g0 (one per quotient-poly chunk)
    tComm = Array.concat (Array.replicate 7 g0XY)

    -- Opening proof lr: 15 (g0, g0) pairs laid out as l.x,l.y,r.x,r.y
    lr = Array.concat (Array.replicate 15 (g0XY <> g0XY))

    delta = g0XY

    sg = g0XY

    -- Flatten dummyEvals into kimchi eval order
    -- (wrap_wire_proof.ml:107-134 Evaluations.to_kimchi):
    --   witness[0..14] | coefficients[0..14] | z | sigma[0..5]
    --   | generic | poseidon | complete_add | mul | emul | endomul_scalar
    flattenVec :: forall n. Vector n { zeta :: WrapField, omegaTimesZeta :: WrapField } -> Array WrapField
    flattenVec v =
      Array.concatMap (\pe -> [ pe.zeta, pe.omegaTimesZeta ])
        (Vector.toUnfoldable v)

    flattenPe :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> Array WrapField
    flattenPe pe = [ pe.zeta, pe.omegaTimesZeta ]

    evalsFlat =
      flattenVec evals.witnessEvals
        <> flattenVec evals.coeffEvals
        <> flattenPe evals.zEvals
        <> flattenVec evals.sigmaEvals
        <> flattenVec evals.indexEvals
  in
    vestaMakeWireProof
      { wComm
      , zComm
      , tComm
      , lr
      , delta
      , sg
      , z1: prf.z1
      , z2: prf.z2
      , evals: evalsFlat
      , ftEval1: evals.ftEval1
      }
