-- | Compute the ft polynomial commitment in-circuit.
-- |
-- | The ft polynomial commitment is:
-- |   ft_comm = perm_scalar * σ_last + Σ_{i} chunk_scalar[i] * t_comm[i]
-- | where chunk_scalar[i] = (1 - ζ^n) * (ζ^max_poly_size)^i
-- |
-- | The bases (σ_last, t_comm chunks) are constants from the verifier index and proof.
-- | The scalars (perm_scalar, chunk scalars) are circuit variables.
-- |
-- | Note: The chunk scalar computation from zeta must be done in the commitment
-- | curve's scalar field. When the circuit field differs (e.g., Fq circuit verifying
-- | Vesta commitments with Fp scalars), chunk scalars should be pre-computed outside
-- | the circuit and passed as inputs. Use `squareN` to compute chunk scalars in-circuit
-- | when the circuit field matches the scalar field (which is the case in the real
-- | step verifier).
-- |
-- | Reference: kimchi/src/verifier.rs ft_comm computation
module Pickles.FtComm
  ( FtCommParams
  , ftCommCircuit
  , squareN
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.MultiscaleKnown (multiscaleKnown)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-- | Parameters for ft polynomial commitment (compile-time constants from VK/proof).
type FtCommParams numChunks f =
  { -- | σ_{PERMUTS-1} commitment from verifier index
    sigmaLast :: AffinePoint (F f)
  , -- | Quotient polynomial commitment chunks from proof
    tCommChunks :: Vector numChunks (AffinePoint (F f))
  , -- | Curve parameters for the commitment curve
    curveParams :: CurveParams f
  }

-- | Compute x^(2^k) via k repeated squarings in-circuit.
-- |
-- | Used to efficiently compute ζ^domain_size and ζ^max_poly_size,
-- | since both domain_size and max_poly_size are powers of 2 in Kimchi.
squareN
  :: forall f c t m
   . CircuitM f c t m
  => Int
  -> FVar f
  -> Snarky c t m (FVar f)
squareN k x
  | k <= 0 = pure x
  | otherwise = do
      x2 <- pure x * pure x
      squareN (k - 1) x2

-- | Compute the ft polynomial commitment in-circuit.
-- |
-- | ft_comm = perm_scalar * σ_last + Σ_{i} chunk_scalar[i] * t_comm[i]
-- |
-- | Takes pre-computed scalars (perm_scalar + chunk scalars) and constant bases.
-- | The chunk scalars should be computed in the commitment curve's scalar field
-- | (which may differ from the circuit field in the Pasta cycle).
ftCommCircuit
  :: forall numChunks f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FtCommParams numChunks f
  -> { permScalar :: FVar f, chunkScalars :: Vector numChunks (FVar f) }
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
ftCommCircuit params { permScalar, chunkScalars } =
  multiscaleKnown @51 params.curveParams
    $ unsafePartial fromJust
    $ NEA.fromArray
    $ Array.cons { scalar: permScalar, base: params.sigmaLast }
    $ Vector.toUnfoldable
    $ Vector.zipWith (\scalar base -> { scalar, base }) chunkScalars params.tCommChunks
