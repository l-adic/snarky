-- | The wrap circuit's private witness. The wrap statement is not part
-- | of it: that arrives separately, as the public input
-- | `Pickles.Wrap.Main.WrapMainInputVar`.
module Pickles.Wrap.Advice
  ( WrapAdvice
  ) where

import Data.Vector (Vector)
import Pickles.Field (WrapField)
import Pickles.Types (AllocEvals, StepIPARounds, WrapIPARounds, WrapProofMessages, WrapProofOpening)
import Pickles.Wrap.Types (PrevProofState)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.Kimchi (Type1, Type2)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)

-- | Private witness data the prover supplies to `wrapMain`, in the
-- | order the circuit allocates it.
-- |
-- | `mpv` is max_proofs_verified, sizing the unfinalized-proof,
-- | step-acc, evals and wrap-domain vectors; `stepChunks` is this
-- | compile's own chunk count, at which the step proof's commitments
-- | arrive. Points are `VestaG`, the step proof's commitment curve.
type WrapAdvice (mpv :: Int) (stepChunks :: Int) =
  { whichBranch :: F WrapField
  , wrapProofState ::
      PrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
  , stepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  -- One stack of bullet-proof challenges per slot, each as wide as
  -- that slot's `max_local_max_proofs_verified`. Nested `Array` rather
  -- than `Vector`: the widths are values, supplied at compile time and
  -- allocated by `Pickles.Typ.perSlotTyp`.
  , oldBpChals :: Array (Array (Vector WrapIPARounds (F WrapField)))
  , evals :: Vector mpv (AllocEvals (F WrapField))
  , wrapDomainIndices :: Vector mpv (F WrapField)
  , openingProof ::
      WrapProofOpening
        StepIPARounds
        (WeierstrassAffinePoint VestaG (F WrapField))
        (Type1 (F WrapField))
  , messages :: WrapProofMessages stepChunks (WeierstrassAffinePoint VestaG (F WrapField))
  }
