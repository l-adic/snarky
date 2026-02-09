-- | Compute the ft polynomial commitment in-circuit.
-- |
-- | Faithful to OCaml `Common.ft_comm` (mina/src/lib/pickles/common.ml:227-246).
-- | Uses shifted scalar ops and Horner accumulation on curve points.
-- |
-- | Reference: kimchi/src/verifier.rs ft_comm computation, common.ml:227-246
module Pickles.FtComm
  ( ftComm
  , squareN
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.Vector (Vector)
import Data.Vector as Vector
import Prim.Int (class Add)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)

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
-- | ft_comm = scale(σ_last, perm) + reduced_t + negate(scale(reduced_t, zeta_to_domain))
-- | where reduced_t = reduce_chunks(t_comm, zeta_to_srs)
-- |
-- | reduce_chunks does Horner accumulation: c[0] + scale(c[1] + scale(..., z), z)
-- |
-- | Reference: mina/src/lib/pickles/common.ml:227-246
ftComm
  :: forall numChunks n1 f t m sf r
   . CircuitM f (KimchiConstraint f) t m
  => Add 1 n1 numChunks
  => { scaleByShifted :: AffinePoint (FVar f) -> sf -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
     | r
     }
  -> { sigmaLast :: AffinePoint (FVar f)
     , tComm :: Vector numChunks (AffinePoint (FVar f))
     , perm :: sf
     , zetaToSrsLength :: sf
     , zetaToDomainSize :: sf
     }
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
ftComm { scaleByShifted } { sigmaLast, tComm, perm, zetaToSrsLength, zetaToDomainSize } = do
  -- Horner reduction of t_comm chunks: c[0] + scale(c[1] + ... + scale(c[n-1], z), z)
  let { last, init } = Vector.unsnoc tComm
  reducedT <- foldM
    ( \acc chunk -> do
        scaled <- scaleByShifted acc zetaToSrsLength
        { p } <- addComplete chunk scaled
        pure p
    )
    last
    (Vector.reverse init)
  -- scale(σ_last, perm)
  permTerm <- scaleByShifted sigmaLast perm
  -- negate(scale(reduced_t, zeta_to_domain))
  zetaDomTerm <- scaleByShifted reducedT zetaToDomainSize
  negZetaDomTerm <- Curves.negate zetaDomTerm
  -- ft_comm = permTerm + reducedT + negZetaDomTerm
  { p: r1 } <- addComplete permTerm reducedT
  { p: result } <- addComplete r1 negZetaDomTerm
  pure result
