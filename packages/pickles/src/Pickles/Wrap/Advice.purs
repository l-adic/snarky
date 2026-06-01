-- | The Wrap circuit's private witness data ("advice").
-- |
-- | In OCaml Pickles (`mina/src/lib/crypto/pickles/wrap_main.ml`), the Wrap
-- | circuit allocates its private witness via 8 `Req.*` requests, answered
-- | by a handler stack. The PureScript port models it as a plain record
-- | (`WrapAdvice`) computed by the prover (`buildWrapAdvice`) and passed by
-- | value into `wrapMain`, which projects each field inside an `exists`
-- | body. There is no bespoke prover transformer and no advice typeclass on
-- | the witness monad — the witness monad is the caller's own `m`.
-- |
-- | Request → field inventory (in OCaml `exists` order, `wrap_main.ml`):
-- |
-- |   1. Req.Which_branch              → whichBranch
-- |   2. Req.Proof_state               → wrapProofState
-- |   3. Req.Step_accs                 → stepAccs
-- |   4. Req.Old_bulletproof_challenges → oldBpChals
-- |   5. Req.Evals                     → evals
-- |   6. Req.Wrap_domain_indices       → wrapDomainIndices
-- |   7. Req.Openings_proof            → openingProof
-- |   8. Req.Messages                  → messages
-- |
-- | The wrap statement (`Wrap.Statement.In_circuit.t`) is NOT a request — it
-- | enters as the public input via `~input_typ` in OCaml. The PureScript
-- | `wrapMain` accepts it as a `WrapInputVar` parameter.
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml lines 138–578
module Pickles.Wrap.Advice
  ( WrapAdvice
  ) where

import Data.Vector (Vector)
import Pickles.Field (WrapField)
import Pickles.Types (StepAllEvals, StepIPARounds, WrapIPARounds, WrapProofMessages, WrapProofOpening)
import Pickles.Wrap.Types (PrevProofState)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.Kimchi (Type1, Type2)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)

-- | Private witness data the wrap prover supplies to `wrapMain`. One
-- | field per `Req.*` request, in the same order `wrap_main.ml`
-- | consumes them.
-- |
-- | Type parameters:
-- |
-- | * `mpv` — max_proofs_verified (varies per compile: N0, N1, or N2);
-- |   sizes the unfinalized-proofs / step-accs / evals / wrap-domain
-- |   vectors.
-- | * `stepChunks` — THIS compile's own num_chunks (the wrap wraps a
-- |   step proof from the current compile, whose commitments are at the
-- |   current compile's chunk count).
-- | * `slots` — the slot-list shape, a `Type -> Type` from
-- |   `Pickles.Wrap.Slots` (`NoSlots`, `Slots1 w`, or `Slots2 w0 w1`).
-- |
-- | The commitment curve is pinned to `VestaG` (the Step proof's
-- | commitment curve) and the field to `WrapField` (= `Vesta.BaseField`
-- | = the native field of the wrap circuit).
type WrapAdvice (mpv :: Int) (stepChunks :: Int) (slots :: Type -> Type) =
  { whichBranch :: F WrapField
  , wrapProofState ::
      PrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
  , stepAccs :: Vector mpv (WeierstrassAffinePoint VestaG (F WrapField))
  , oldBpChals :: slots (Vector WrapIPARounds (F WrapField))
  , evals :: Vector mpv (StepAllEvals (F WrapField))
  , wrapDomainIndices :: Vector mpv (F WrapField)
  , openingProof ::
      WrapProofOpening
        StepIPARounds
        (WeierstrassAffinePoint VestaG (F WrapField))
        (Type1 (F WrapField))
  , messages :: WrapProofMessages stepChunks (WeierstrassAffinePoint VestaG (F WrapField))
  }
