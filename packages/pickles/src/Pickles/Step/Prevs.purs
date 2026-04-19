-- | Heterogeneous per-prev container for step_main.
-- |
-- | OCaml's `step_main` accepts a rule whose `prevs` is an hlist of
-- | `Tag.t`s, each carrying its own `max_proofs_verified`. The per-prev
-- | `Per_proof_witness.t` is sized by THAT prev's `max_proofs_verified`
-- | (see `per_proof_witness.ml:87-91`: `prev_challenges` outer length =
-- | `'max_proofs_verified`, `prev_challenge_polynomial_commitments`
-- | outer length = same).
-- |
-- | The older `Vector n StepPerProofWitness` encoding instantiates every
-- | prev's witness with the SAME `n` (self's `max_proofs_verified`),
-- | which only works for self-recursive rules where all prevs
-- | coincidentally share the same `n`. For genuinely heterogeneous
-- | configurations like `Tree_proof_return`
-- | (`prevs = [No_recursion_return.tag; self]`, Ns = `[0; 2]`), the
-- | uniform encoding over-allocates prev-sized fields (extra on-curve
-- | checks, extra witnesses) and breaks byte-identity with OCaml.
-- |
-- | This module encodes the per-prev spec as a type-level list of
-- | `max_proofs_verified` values (`PrevsSpecCons n rest` / `PrevsSpecNil`)
-- | and provides a single class `PrevsCarrier` that:
-- |
-- |  (1) derives the concrete nested-tuple carrier type from the spec
-- |      (mapping `PrevsSpecCons n rest -> Tuple (SPPW n …) rest_carrier`);
-- |  (2) traverses that carrier with a rank-2 callback that receives each
-- |      slot's `StepPerProofWitness n_i ds dw f sf b` with `n_i` in scope.
-- |
-- | Construction of a carrier is compositional via the existing
-- | `CircuitType` / `CheckedType` instances for `Tuple` — no dedicated
-- | "allocate" method is needed; `exists` at a tuple type resolves
-- | structurally to each slot's own SPPW `CircuitType` instance.
-- |
-- | This is a step-side analog of `Pickles.Wrap.Slots` (the wrap-side
-- | `Slots2 w0 w1` encoding for bulletproof-challenge stacks). The type
-- | encoding is structurally similar but intentionally separate — the
-- | payloads differ (wrap has a uniform element type `a`; step has a
-- | heterogeneous `SPPW n_i …` per slot).
-- |
-- | Reference:
-- |   mina/src/lib/crypto/pickles/per_proof_witness.ml:80-95
-- |   mina/src/lib/crypto/pickles/step_main.ml:353-366 (exists_prevs)
module Pickles.Step.Prevs
  ( PrevsSpecNil
  , PrevsSpecCons
  , StepSlot(..)
  , class PrevsCarrier
  , traversePrevsA
  , replicatePrevsCarrier
  ) where

import Prelude

import Data.Fin (Finite, finZero, shiftSucc)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Types (PaddedLength, StepPerProofWitness)
import Prim.Int (class Add)

--------------------------------------------------------------------------------
-- Type-level list of per-prev max_proofs_verified values
--------------------------------------------------------------------------------

-- | Empty prev list: the rule verifies zero previous proofs.
-- | Equivalent to `max_proofs_verified = N0` in OCaml. Phantom type;
-- | no inhabitants (used only at the type level).
data PrevsSpecNil

-- | Cons a per-prev `max_proofs_verified = n` onto the head of the
-- | list. `rest` is the spec for the remaining prevs.
-- |
-- | Shapes for the 4 circuit-diff fixtures:
-- | * Add_one_return   : `PrevsSpecNil`
-- | * Simple_chain N1  : `PrevsSpecCons 1 PrevsSpecNil`
-- | * Simple_chain N2  : `PrevsSpecCons 2 (PrevsSpecCons 2 PrevsSpecNil)`
-- | * Tree_proof_return: `PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)`
data PrevsSpecCons (n :: Int) (rest :: Type)

--------------------------------------------------------------------------------
-- Per-slot payload
--------------------------------------------------------------------------------

-- | All runtime data for one step-prev slot, bundled. Currently holds
-- | just the per-proof witness; extensible over time (e.g. per-slot
-- | wrap VK commitments for heterogeneous-prev rules like
-- | `Tree_proof_return`, where slot 0's wrap VK is from
-- | `No_recursion_return` and slot 1's is self's).
-- |
-- | Bundling lets us thread a single rack (one spec-indexed carrier of
-- | `StepSlot`s) through the prover stack rather than maintaining
-- | multiple co-indexed racks à la OCaml's `H4.T(Tag).t` /
-- | `H1.T(Nat).t` / `H1.T(Optional_wrap_key).t`. OCaml keeps them
-- | separate due to hlist ergonomics; PureScript can encode the same
-- | information as type parameters on a single newtype.
newtype StepSlot n ds dw f sf b = StepSlot
  { sppw :: StepPerProofWitness n ds dw f sf b
  }

--------------------------------------------------------------------------------
-- The carrier class
--------------------------------------------------------------------------------

-- | Maps a `PrevsSpec*` spec to:
-- |  (a) a `len` — the prev count (via fundep);
-- |  (b) a `carrier` — the concrete nested-tuple type carrying one
-- |      `StepPerProofWitness n_i ds dw f sf b` per prev slot (via fundep);
-- |  (c) a traversal `traversePrevsA` — a rank-2 fold that walks the
-- |      carrier in slot order, invoking a callback with that slot's
-- |      typed SPPW.
-- |
-- | Carrier derivation:
-- |   spec                                       → carrier
-- |   PrevsSpecNil                               → Unit
-- |   PrevsSpecCons n PrevsSpecNil               → Tuple (SPPW n ds dw f sf b) Unit
-- |   PrevsSpecCons n0 (PrevsSpecCons n1 PrevsSpecNil)
-- |      → Tuple (SPPW n0 …) (Tuple (SPPW n1 …) Unit)
class PrevsCarrier
  :: Type -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Constraint
class
  PrevsCarrier spec ds dw f sf b len carrier
  | spec ds dw f sf b -> len carrier
  where
  -- | Walk the carrier in slot order, invoking the callback per slot.
  -- | The callback's `forall n. Reflectable n Int =>` prefix lets each
  -- | invocation access its slot's own `n_i` — so
  -- | `pw.prevSgs :: Vector n_i …` and friends are correctly sized per
  -- | slot.
  -- |
  -- | The `Finite len` index passed to the callback is the ABSOLUTE
  -- | slot position (0-based, 0 through len-1), lifted through each
  -- | recursive level's `shiftSucc` so the callback always sees the
  -- | top-level bound.
  traversePrevsA
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Finite len
         -> StepSlot n ds dw f sf b
         -> m result
       )
    -> carrier
    -> m (Vector len result)

  -- | Build a carrier from a rank-2 polymorphic dummy slot. Each slot
  -- | auto-specializes the dummy to its own `n_i`. For homogeneous
  -- | specs (Simple_chain-style), the dummy is just replicated across
  -- | all slots; for heterogeneous specs the rank-2 polymorphism gives
  -- | each slot its correctly-sized version.
  -- |
  -- | Callers typically pass a dummy built to depend on its own `n`:
  -- |   `dummySlot = StepSlot { sppw: StepPerProofWitness { …, prevSgs = Vector.replicate g0, … } }`
  -- | `Vector.replicate` inside the SPPW expands to `Vector n_i _` at
  -- | each slot.
  replicatePrevsCarrier
    :: ( forall n
          . Reflectable n Int
         => StepSlot n ds dw f sf b
       )
    -> carrier

instance PrevsCarrier PrevsSpecNil ds dw f sf b 0 Unit where
  traversePrevsA _ _ = pure Vector.nil
  replicatePrevsCarrier _ = unit

instance
  ( PrevsCarrier rest ds dw f sf b restLen rcarrier
  , Add restLen 1 len
  , Reflectable n Int
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  PrevsCarrier
    (PrevsSpecCons n rest) ds dw f sf b len
    (Tuple (StepSlot n ds dw f sf b) rcarrier)
  where
  traversePrevsA f (Tuple here rest) =
    -- `hereIdx :: Finite len` — slot 0 of `len`. `finZero`'s
    -- `Add n 1 n1` constraint discharges with `n = restLen`, `n1 = len`
    -- (so `len ≥ 1` by construction at every Cons instance).
    --
    -- The lambda `\i' pw -> f (shiftSucc i') pw` lifts recursive-call
    -- indices from `Finite restLen` up to `Finite len` via `shiftSucc`.
    -- Each recursive layer's closure chain accumulates shifts so the
    -- top-level callback always receives the absolute slot position.
    Vector.cons
      <$> f (finZero :: Finite len) here
      <*> traversePrevsA @rest (\i' pw -> f (shiftSucc i') pw) rest

  replicatePrevsCarrier dummyPPW =
    -- `dummyPPW` is rank-2 in `n`; at the `here` slot it specializes to
    -- `StepPerProofWitness n ds dw f sf b` (where `n` is this Cons
    -- instance's head Int), and at the recursive call it auto-specializes
    -- to each of `rest`'s per-slot Ns.
    Tuple dummyPPW (replicatePrevsCarrier @rest dummyPPW)
