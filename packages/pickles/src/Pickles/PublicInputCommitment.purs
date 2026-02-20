module Pickles.PublicInputCommitment (publicInputCommitment) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Reflectable (class Reflectable)
import Pickles.MultiscaleKnown (multiscaleKnown)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-- | Compute x_hat = public input commitment in-circuit.
-- |
-- | Given public input circuit variables and constant lagrange commitment bases,
-- | computes: negate(multiscaleKnown(zip(publicInput, lagrangeComms))) + H
-- |
-- | The lagrange commitments and blinding generator H are compile-time constants
-- | (precomputed from the SRS/verifier index).
publicInputCommitment
  :: forall @nChunks @sDiv2Bits f n bitsUsed t m _l _afterBits
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits _afterBits n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => CurveParams f
  -> NonEmptyArray { scalar :: FVar f, base :: AffinePoint (F f) }
  -> AffinePoint (F f)
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
publicInputCommitment params pairs blindingH = do
  msm <- multiscaleKnown @nChunks @sDiv2Bits params pairs
  negMsm <- Curves.negate msm
  _.p <$> addComplete negMsm (constPoint blindingH)
  where
  constPoint :: AffinePoint (F f) -> AffinePoint (FVar f)
  constPoint { x: F x, y: F y } = { x: const_ x, y: const_ y }
