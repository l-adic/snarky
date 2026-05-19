-- | Advisory monad for the Wrap circuit's private witness data.
-- |
-- | In OCaml Pickles (`mina/src/lib/crypto/pickles/wrap_main.ml`), the Wrap
-- | circuit allocates its private witness via 8 `Req.*` requests. Each method
-- | here corresponds to one OCaml `exists ~request:Req.*` call, in the same
-- | source order so the resulting constraint system has the same allocation
-- | layout.
-- |
-- | Request inventory (in OCaml `exists` order):
-- |
-- |   1. Req.Which_branch         — single Field selecting the active branch
-- |   2. Req.Proof_state          — combined `mpv` unfinalized proofs +
-- |                                 messages_for_next_step_proof
-- |   3. Req.Step_accs            — Vector of `mpv` step accumulators (curve points)
-- |   4. Req.Old_bulletproof_challenges
-- |                               — heterogeneous bp-chals grouped by slot
-- |                                 (`Max_widths_by_slot.maxes`)
-- |   5. Req.Evals                — Vector of `mpv` `StepAllEvals`
-- |   6. Req.Wrap_domain_indices  — Vector of `mpv` Field indices
-- |   7. Req.Openings_proof       — single `WrapProofOpening` (Type1 scalars)
-- |   8. Req.Messages             — single `WrapProofMessages`
-- |
-- | The wrap statement (`Wrap.Statement.In_circuit.t`) is NOT a request — it
-- | enters as the public input via `~input_typ` in OCaml. The PureScript
-- | `wrapMain` accepts it as a `WrapInputVar` parameter.
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml lines 138–578
module Pickles.Wrap.Advice
  ( -- The new advice class used by `Pickles.Wrap.Main.wrapMain`.
    class WrapWitnessM
  , getWhichBranch
  , getWrapProofState
  , getStepAccs
  , getOldBulletproofChallenges
  , getEvals
  , getWrapDomainIndices
  , getOpeningProof
  , getMessages
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.Types (StepAllEvals, StepIPARounds, WrapIPARounds, WrapProofMessages, WrapProofOpening)
import Pickles.Wrap.Slots (class PadSlots)
import Pickles.Wrap.Types (PrevProofState)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.Kimchi (Type1, Type2)
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)

-- | Advisory monad for the Wrap circuit.
-- |
-- | Parameters:
-- | - `branches`: number of step circuit variants (one_hot length)
-- | - `mpv`: max_proofs_verified (always 2 in Pickles); determines the size
-- |          of the unfinalized-proofs / step-accs / evals / wrap-domain
-- |          vectors.
-- | - `slot0Width`, `slot1Width`: per-slot widths of `Max_widths_by_slot`,
-- |          determining the shape of `Req.Old_bulletproof_challenges`.
-- | - `g`: commitment curve of the Step proof being verified (= `VestaG`)
-- | - `f`: base field of `g` — uniquely determined via `WeierstrassCurve f g`
-- |        (= `Vesta.BaseField` = `Field`)
-- | - `slots`: the slot-list shape, a higher-kinded type constructor
-- |        (`Type -> Type`) from `Pickles.Wrap.Slots`. Concretely one of
-- |        `NoSlots`, `Slots1 w`, or `Slots2 w0 w1` per library use.
-- |        The class method `getOldBulletproofChallenges` returns a
-- |        `slots`-shaped structure that inducts over in `wrapMain`.
-- | - `m`: base monad (Effect for compilation, WrapProverT for proving)
class
  ( Monad m
  , WeierstrassCurve f g
  ) <=
  WrapWitnessM
    (branches :: Int)
    (mpv :: Int)
    (stepChunks :: Int)
    (slots :: Type -> Type)
    g
    f
    m
  | g -> f
  , slots -> mpv
  where
  -- | OCaml: `Req.Which_branch` (`wrap_main.ml:223`).
  getWhichBranch :: Unit -> m (F f)

  -- | OCaml: `Req.Proof_state` (`wrap_main.ml:267`). Returns the combined
  -- | `mpv` unfinalized proofs (`Type2 of Field.t` — a single raw field per
  -- | deferred value, NOT pre-split) and the digest `messages_for_next_step_proof`
  -- | field. The split into `(sDiv2, sOdd)` happens later via
  -- | `splitFieldCircuit` in `pack_statement`.
  getWrapProofState
    :: Unit
    -> m
         ( PrevProofState
             mpv
             (Type2 (F f))
             (F f)
             Boolean
         )

  -- | OCaml: `Req.Step_accs` (`wrap_main.ml:369`). Vector of `mpv` step
  -- | accumulators (commitment-curve affine points).
  getStepAccs :: Unit -> m (Vector mpv (WeierstrassAffinePoint g (F f)))

  -- | OCaml: `Req.Old_bulletproof_challenges` (`wrap_main.ml:400`). Returns
  -- | a `slots`-shaped structure: `NoSlots` (empty), `Slots1 w` (one slot),
  -- | or `Slots2 w0 w1` (two slots), mirroring OCaml's
  -- | `Max_widths_by_slot.maxes`. The `PadSlots` class provides the
  -- | structural traversal that consumes this value.
  -- |
  -- | The inner element type is `F f` (the value form); `exists` in
  -- | `wrap_main` converts this to the var form
  -- | `slots (Vector WrapIPARounds (FVar f))` via the `CircuitType`
  -- | instances for `Product` and `Const Unit` defined in
  -- | `Snarky.Circuit.Types`.
  getOldBulletproofChallenges
    :: Unit
    -> m (slots (Vector WrapIPARounds (F f)))

  -- | OCaml: `Req.Evals` (`wrap_main.ml:415`). Vector of `mpv`
  -- | `StepAllEvals`, one per previous wrap proof.
  getEvals :: Unit -> m (Vector mpv (StepAllEvals (F f)))

  -- | OCaml: `Req.Wrap_domain_indices` (`wrap_main.ml:423`). Vector of `mpv`
  -- | indices into `Wrap_verifier.all_possible_domains`.
  getWrapDomainIndices :: Unit -> m (Vector mpv (F f))

  -- | OCaml: `Req.Openings_proof` (`wrap_main.ml:531`). The full bulletproof
  -- | opening transported through Type1 shifted-value coercion.
  getOpeningProof
    :: Unit
    -> m
         ( WrapProofOpening
             StepIPARounds
             (WeierstrassAffinePoint g (F f))
             (Type1 (F f))
         )

  -- | OCaml: `Req.Messages` (`wrap_main.ml:540`). Protocol commitments for
  -- | the IVP step.
  getMessages
    :: Unit
    -> m
         ( WrapProofMessages stepChunks
             (WeierstrassAffinePoint g (F f))
         )

-- | Compilation instance: never invoked, exists only to satisfy the constraint
-- | during `compile` (where the base monad is `Effect`). If any method here
-- | actually fires it indicates a bug — the throw makes that obvious.
instance
  ( WeierstrassCurve f g
  , Reflectable branches Int
  , Reflectable mpv Int
  , PadSlots slots mpv
  ) =>
  WrapWitnessM branches mpv stepChunks slots g f Effect where
  getWhichBranch _ = throw "impossible! getWhichBranch called during compilation"
  getWrapProofState _ = throw "impossible! getWrapProofState called during compilation"
  getStepAccs _ = throw "impossible! getStepAccs called during compilation"
  getOldBulletproofChallenges _ = throw "impossible! getOldBulletproofChallenges called during compilation"
  getEvals _ = throw "impossible! getEvals called during compilation"
  getWrapDomainIndices _ = throw "impossible! getWrapDomainIndices called during compilation"
  getOpeningProof _ = throw "impossible! getOpeningProof called during compilation"
  getMessages _ = throw "impossible! getMessages called during compilation"

