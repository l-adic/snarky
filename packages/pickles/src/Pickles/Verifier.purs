-- | Kimchi proof verifier circuit.
-- |
-- | This module implements the in-circuit verification of a single Kimchi proof.
-- | The verifier takes challenges as public inputs (for cross-curve verification)
-- | and:
-- | 1. Computes lrProd from L/R pairs and challenges
-- | 2. Computes b from challenges
-- | 3. Verifies the IPA opening equation
-- | 4. Outputs the challenges for deferred out-of-circuit sg verification
-- |
-- | Note: In the Pickles recursion pattern, the sponge-derived values (challenges,
-- | U, c) are computed outside the circuit and passed as public inputs. This is
-- | because the sponge operates on the proof's native field, which may be foreign
-- | to the verifier circuit's field.
module Pickles.Verifier
  ( verify
  , VerifyInput
  , module Types
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Pickles.BulletproofVerifier (combineSplitCommitments, lrProdCircuit)
import Pickles.Commitments (computeBCircuit)
import Pickles.Verifier.Types (DeferredCheck, OpeningProof, ProofMessages, VerifierOutput) as Types
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2, splitFieldVar)
import Snarky.Circuit.Types (BoolVar, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type2)

--------------------------------------------------------------------------------
-- | Verify Input
--------------------------------------------------------------------------------

-- | Input to the verifier circuit.
-- |
-- | In the Pickles recursion pattern, challenges and other sponge-derived values
-- | are public inputs (computed outside the circuit due to foreign field).
-- |
-- | Type parameters:
-- | - d: number of IPA rounds (= bulletproof challenge count)
-- | - n: number of polynomial commitments to batch
-- | - f: field value type (far f for circuit, F f for test values)
-- | - b: boolean type (BoolVar f for circuit, Boolean for test values)
type VerifyInput d n f b =
  { -- Batching scalar for polynomial commitments
    xi :: f

  -- Polynomial commitments to batch
  , commitments :: Vector n (AffinePoint f)

  -- Combined inner product
  , combinedInnerProduct :: f

  -- Opening proof
  , opening ::
      { lr :: Vector d { l :: AffinePoint f, r :: AffinePoint f }
      , delta :: AffinePoint f
      , z1 :: Type2 f b
      , z2 :: Type2 f b
      , sg :: AffinePoint f
      }

  -- Evaluation points for computing b
  , zeta :: f
  , zetaOmega :: f
  , evalscale :: f -- u: for combining evaluations at zeta and zeta*omega

  -- SRS generator H
  , h :: AffinePoint f

  -- Public inputs (sponge-derived, computed outside circuit)
  , challenges :: Vector d f -- IPA challenges (endo-mapped, full field elements)
  , u :: AffinePoint f -- U = groupMap(squeeze(sponge after absorbing CIP))
  , c :: f -- c = squeeze_scalar(sponge after absorbing delta)
  }

--------------------------------------------------------------------------------
-- | Main Verify Function
--------------------------------------------------------------------------------

-- | Verify a Kimchi proof in-circuit.
-- |
-- | This performs the IPA verification with pre-computed challenges:
-- | 1. Compute lrProd from L/R pairs and challenges (using lrProdCircuit)
-- | 2. Compute b from challenges (using computeBCircuit)
-- | 3. Combine polynomial commitments
-- | 4. Build Q = combined + cip*U + lrProd
-- | 5. Verify IPA equation: endo(Q, c) + delta = z1*(sg + b*U) + z2*H
-- | 6. Return challenges for deferred sg verification
-- |
-- | The expensive sg verification (sg = MSM(SRS.g, b_poly_coefficients(challenges)))
-- | is deferred to out-of-circuit.
verify
  :: forall @d @d' @n @n' @nChunks f f' t m
   . Reflectable d Int
  => Reflectable n Int
  => Add 1 d' d
  => Add 1 n' n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Mul 5 nChunks 255
  => Reflectable nChunks Int
  => HasEndo f f'
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => VerifyInput d n (FVar f) (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (Types.VerifierOutput d (FVar f))
verify input = do
  -- Step 1: Compute lrProd from L/R pairs and pre-computed challenges
  lrProd <- lrProdCircuit @d @d' @nChunks input.opening.lr input.challenges

  -- Step 2: Compute b from challenges
  b <- computeBCircuit
    { challenges: input.challenges
    , zeta: input.zeta
    , zetaOmega: input.zetaOmega
    , evalscale: input.evalscale
    }

  -- Step 3: Combine polynomial commitments
  combined <- combineSplitCommitments @n input.xi input.commitments

  -- Step 4: Build Q = combined + cip*U + lrProd
  cipType2 <- splitFieldVar input.combinedInnerProduct
  uTimesCip <- scaleFast2 @nChunks input.u cipType2
  { p: pPrime } <- addComplete combined uTimesCip
  { p: q } <- addComplete pPrime lrProd

  -- Step 5: Verify IPA equation
  -- LHS = endo(q, c) + delta
  qTimesC <- endo q input.c
  { p: lhs } <- addComplete qTimesC input.opening.delta

  -- RHS = scaleFast2(sg + scaleFast2(u, b), z1) + scaleFast2(h, z2)
  bType2 <- splitFieldVar b
  uTimesB <- scaleFast2 @nChunks input.u bType2
  { p: sgPlusUB } <- addComplete input.opening.sg uTimesB
  term1 <- scaleFast2 @nChunks sgPlusUB input.opening.z1
  term2 <- scaleFast2 @nChunks input.h input.opening.z2
  { p: rhs } <- addComplete term1 term2

  -- Assert LHS == RHS
  EllipticCurve.assertEqual lhs rhs

  -- Step 6: Return challenges for deferred sg verification
  pure
    { deferredCheck: { challenges: input.challenges }
    , sg: input.opening.sg
    }