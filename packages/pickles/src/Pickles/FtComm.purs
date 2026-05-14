-- | Compute the ft polynomial commitment in-circuit.
-- |
-- | Faithful to OCaml `Common.ft_comm` (mina/src/lib/pickles/common.ml:227-246).
-- | Uses shifted scalar ops and Horner accumulation on curve points.
-- |
-- | Reference: kimchi/src/verifier.rs ft_comm computation, common.ml:227-246
module Pickles.FtComm
  ( ftComm
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.Vector (Vector)
import Data.Vector as Vector
import Prim.Int (class Add)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, label)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Compute the ft polynomial commitment in-circuit.
-- |
-- | ft_comm = scale(σ_last, perm) + reduced_t + negate(scale(reduced_t, zeta_to_domain))
-- | where reduced_t = reduce_chunks(t_comm, zeta_to_srs)
-- |
-- | reduce_chunks does Horner accumulation: c[0] + scale(c[1] + scale(..., z), z)
-- |
-- | Reference: mina/src/lib/pickles/common.ml:227-246
ftComm
  :: forall numChunks numChunksPred tCommLen tCommLenPred f t m sf r
   . CircuitM f (KimchiConstraint f) t m
  => Add 1 numChunksPred numChunks
  => Add 1 tCommLenPred tCommLen
  => { scaleByShifted :: AffinePoint (FVar f) -> sf -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
     | r
     }
  -> { sigmaLast :: Vector numChunks (AffinePoint (FVar f))
     , tComm :: Vector tCommLen (AffinePoint (FVar f))
     , perm :: sf
     , zetaToSrsLength :: sf
     , zetaToDomainSize :: sf
     }
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
ftComm { scaleByShifted } { sigmaLast, tComm, perm, zetaToSrsLength, zetaToDomainSize } = label "ft-comm" do
  -- OCaml order (common.ml:307-326): both `sigma_comm_last` and `t_comm`
  -- are chunk arrays. Each one is collapsed via `reduce_chunks` (xi-Horner
  -- with `zeta_to_srs_length`), THEN scaled / combined:
  --   1. sigma_comm_last_reduced = reduce_chunks sigma_comm_last
  --   2. f_comm                  = scale sigma_comm_last_reduced plonk.perm
  --   3. chunked_t_comm          = reduce_chunks t_comm
  --   4. Expression: f_comm + chunked_t_comm + negate(scale chunked_t_comm zeta_to_domain)
  --      Due to right-to-left OCaml argument evaluation:
  --        a. negate(scale chunked_t_comm zeta_to_domain)  [right arg of outer +]
  --        b. f_comm + chunked_t_comm                      [left arg of outer +]
  --        c. result + negated                              [outer +]

  -- Step 0: reduce_chunks sigmaLast (Horner over zetaToSrsLength).
  reducedSigmaLast <- hornerReduce sigmaLast
  -- Step 1: scale(σ_last_reduced, perm)
  fComm <- scaleByShifted reducedSigmaLast perm
  -- Step 2: Horner reduction of t_comm chunks
  chunkedTComm <- hornerReduce tComm
  -- Step 3a: negate(scale(chunked_t_comm, zeta_to_domain)) [right-to-left: evaluated first]
  zetaDomTerm <- scaleByShifted chunkedTComm zetaToDomainSize
  negZetaDomTerm <- Curves.negate zetaDomTerm
  -- Step 3b: f_comm + chunked_t_comm [evaluated second]
  { p: r1 } <- addComplete fComm chunkedTComm
  -- Step 3c: result + negated
  { p: result } <- addComplete r1 negZetaDomTerm
  pure result
  where
  -- `reduce_chunks` from OCaml `common.ml:311-318`:
  -- res = comm[n-1]; for i = n-2 downto 0: res = comm[i] + scale res zetaToSrsLength
  hornerReduce
    :: forall k kPred
     . Add 1 kPred k
    => Vector k (AffinePoint (FVar f))
    -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  hornerReduce v =
    let
      { last, init } = Vector.unsnoc v
    in
      foldM
        ( \acc chunk -> do
            scaled <- scaleByShifted acc zetaToSrsLength
            { p } <- addComplete chunk scaled
            pure p
        )
        last
        (Vector.reverse init)
