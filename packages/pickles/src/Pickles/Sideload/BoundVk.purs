-- | A side-loaded verification key a rule has tied to its own
-- | statement, which is what makes a side-loaded slot certify which
-- | child it verified rather than any child the prover chose.
-- |
-- | `bindVk` is the only way to obtain a `BoundVk`: it asserts the key's
-- | digest equals one the rule supplies. The digest is Mina's
-- | `digest_vk`, the hash a zkApp account stores for its verification
-- | key, so a rule can bind against a digest Mina computed; `digestVk`
-- | computes it outside the circuit.
module Pickles.Sideload.BoundVk
  ( module Reexport
  , bindVk
  , digestVk
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM, foldl)
import Data.Newtype (unwrap)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.Sideload.BoundVk.Internal (BoundVk(..))
import Pickles.Sideload.BoundVk.Internal (BoundVk) as Reexport
import Pickles.Sideload.VerificationKey (VerificationKey(..))
import Pickles.Types (WrapVkChunks)
import Pickles.VerificationKey as VK
import RandomOracle.DomainSeparator (initWithDomain)
import RandomOracle.Input as Input
import RandomOracle.Sponge (SpongeState(..))
import RandomOracle.Sponge as Sponge
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F, FVar, Snarky, add_, assertEqual_, label, scale_)
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))

-- | Mina's `Hash_prefix_states.side_loaded_vk`.
sideLoadedVkPrefix :: String
sideLoadedVkPrefix = "MinaSideLoadedVk"

-- | The wrap index's coordinates in `digest_vk`'s order: `sigma`,
-- | `coeff`, then `index`, each point `x` before `y`.
wrapIndexFields
  :: forall f
   . VK.VerificationKey WrapVkChunks (WeierstrassAffinePoint Pallas.G f)
  -> Array f
wrapIndexFields (VK.VerificationKey r) =
  Array.concatMap coordinates
    (commitments r.sigma <> commitments r.coeff <> commitments r.index)
  where
  commitments :: forall n c. Vector n c -> Array c
  commitments = Vector.toUnfoldable

  coordinates c = Array.concatMap (\(WeierstrassAffinePoint p) -> [ p.x, p.y ])
    (Vector.toUnfoldable (unwrap c))

-- | The two one-hot fields' six bits, `maxProofsVerified` first.
oneHotBits :: forall f b. VerificationKey WrapVkChunks f b -> Vector 6 b
oneHotBits (VerificationKey r) =
  r.maxProofsVerified `Vector.append` r.actualWrapDomainSize

-- | Mina's `digest_vk` of a side-loaded key: Poseidon from the
-- | `MinaSideLoadedVk` prefix over the wrap index's coordinates, then
-- | the six one-hot bits packed into one field.
digestVk :: VerificationKey WrapVkChunks (F StepField) Boolean -> StepField
digestVk vk@(VerificationKey r) =
  let
    fields = Input.packToFields
      { fieldElements: map unwrap (wrapIndexFields r.wrapIndex)
      , packeds: map (\b -> { value: if b then one else zero, length: 1 })
          (Vector.toUnfoldable (oneHotBits vk))
      }
    sponge = foldl (\sp x -> Sponge.absorb x sp)
      (Sponge.create (initWithDomain sideLoadedVkPrefix))
      fields
  in
    (Sponge.squeeze sponge).result

-- | Asserts that the key's `digest_vk` equals `digest`, and returns the
-- | key as bound.
bindVk
  :: forall r
   . FVar StepField
  -> VerificationKey WrapVkChunks (FVar StepField) (BoolVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r BoundVk
bindVk digest vk@(VerificationKey r) = label "bind_vk" do
  let
    -- One field holds the six bits, the first most significant, as
    -- `pack_to_fields` accumulates them.
    { head, tail } = Vector.uncons (map coerce (oneHotBits vk) :: Vector 6 (FVar StepField))
    packed = foldl (\acc b -> add_ (scale_ (one + one) acc) b) head tail
    sponge0 = CircuitSponge.spongeFromConstants
      { state: initWithDomain sideLoadedVkPrefix
      , spongeState: Squeezed (unsafeFinite 0)
      }
  sponge <- foldM (\sp x -> CircuitSponge.absorb x sp) sponge0
    (wrapIndexFields r.wrapIndex `Array.snoc` packed)
  { result } <- CircuitSponge.squeeze sponge
  assertEqual_ result digest
  pure (BoundVk vk)
