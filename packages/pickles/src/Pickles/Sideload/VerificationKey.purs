-- | A child's wrap verification key at the protocol level: only the
-- | data the parent's step circuit walks. The `f` and `b` parameters
-- | pick the value form, `(F StepField, Boolean)`, or the var form,
-- | `(FVar f, BoolVar f)`, out of the one type.
-- |
-- | The kimchi runtime handle is not here; it lives in
-- | `Pickles.Sideload.Bundle`.
module Pickles.Sideload.VerificationKey
  ( VerificationKey(..)
  , compileDummy
  , mkVerificationKey
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.ProofsVerified (ProofsVerified(..), ProofsVerifiedCount, proofsVerifiedToBoolVec)
import Pickles.Types (ChunkedCommitment(..))
import Pickles.VerificationKey as VK
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, F(..), FVar, assertExactlyOne_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The three circuit-visible fields of a side-loaded VK, serialised
-- | in the order written here — `maxProofsVerified`,
-- | `actualWrapDomainSize`, `wrapIndex` — which is not the alphabetical
-- | order a bare record would pick up. Hence the newtype.
-- |
-- | `actualWrapDomainSize` is not a domain size in the integer sense.
-- | Side-loaded wrap circuits support exactly three domain sizes,
-- | 2^13, 2^14 and 2^15, corresponding one to one with
-- | `maxProofsVerified ∈ {N0, N1, N2}`, so the field says which of the
-- | three is in play, tagged by the enum rather than by the log2.
-- |
-- | Both enums are one-hot `Vector ProofsVerifiedCount b`: the var form
-- | has boolean wires and cannot pattern-match on an enum.
newtype VerificationKey :: Int -> Type -> Type -> Type
newtype VerificationKey slotVkChunks f b = VerificationKey
  { maxProofsVerified :: Vector ProofsVerifiedCount b
  , actualWrapDomainSize :: Vector ProofsVerifiedCount b
  , wrapIndex :: VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G f)
  }

derive instance Generic (VerificationKey slotVkChunks f b) _

-- | Bridges the value saturation `(F g, Boolean)` to the var
-- | saturation `(FVar g, BoolVar g)`. Concrete-headed (rather than
-- | parametric in the row elements) because the inner
-- | `WeierstrassAffinePoint`'s `CircuitType` instance is itself keyed
-- | on `(F f) -> (FVar f)`, not on arbitrary `a -> var`.
instance
  ( PrimeField g
  , Reflectable slotVkChunks Int
  ) =>
  CircuitType g
    (VerificationKey slotVkChunks (F g) Boolean)
    (VerificationKey slotVkChunks (FVar g) (BoolVar g)) where
  sizeInFields pf _ =
    genericSizeInFields pf
      (Proxy @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (F g)))))
  valueToFields (VerificationKey r) =
    genericValueToFields (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (F g)))
      tup = genericFieldsToValue fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            VerificationKey { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup
  varToFields (VerificationKey r) =
    genericVarToFields
      @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (F g))))
      (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector ProofsVerifiedCount (BoolVar g)) (Vector ProofsVerifiedCount (BoolVar g)) (VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (FVar g)))
      tup = genericFieldsToVar
        @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (F g))))
        fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            VerificationKey { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup

-- | Each one-hot field's boolean checks are immediately followed by
-- | its `assertExactlyOne_`, and `wrapIndex`'s on-curve checks come
-- | last. That emission order is part of the circuit.
instance
  ( CheckedType g c (WeierstrassAffinePoint Pallas.G (FVar g))
  , CheckedType g c (BoolVar g)
  , PrimeField g
  , BasicSystem g c
  ) =>
  CheckedType g c (VerificationKey slotVkChunks (FVar g) (BoolVar g)) where
  check (VerificationKey r) = do
    label "vk_max_proofs_verified" do
      label "boolean_checks" $ check r.maxProofsVerified
      label "exactly_one"
        $ assertExactlyOne_ (Vector.toUnfoldable r.maxProofsVerified)
    label "vk_actual_wrap_domain_size" do
      label "boolean_checks" $ check r.actualWrapDomainSize
      label "exactly_one"
        $ assertExactlyOne_ (Vector.toUnfoldable r.actualWrapDomainSize)
    label "vk_wrap_index" $ check r.wrapIndex

-- | A placeholder sized for the largest side-loaded VK, both enums at
-- | `N2`; a smaller runtime VK masks down through its own one-hot
-- | bits. It feeds `exists`, and the constraint-system pass never reads
-- | the point coordinates.
compileDummy
  :: forall slotVkChunks
   . Reflectable slotVkChunks Int
  => VerificationKey slotVkChunks (F StepField) Boolean
compileDummy = mkVerificationKey
  { maxProofsVerified: N2
  , actualWrapDomainSize: N2
  , wrapIndex:
      VK.VerificationKey
        { sigma: Vector.replicate (ChunkedCommitment (Vector.replicate g))
        , coeff: Vector.replicate (ChunkedCommitment (Vector.replicate g))
        , index: Vector.replicate (ChunkedCommitment (Vector.replicate g))
        }
  }
  where
  -- Off-curve placeholder.
  g :: WeierstrassAffinePoint Pallas.G (F StepField)
  g = WeierstrassAffinePoint { x: F zero, y: F zero }

-- | Builds the two one-hot fields from the `ProofsVerified` enum.
mkVerificationKey
  :: forall slotVkChunks
   . { maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     , wrapIndex :: VK.VerificationKey slotVkChunks (WeierstrassAffinePoint Pallas.G (F StepField))
     }
  -> VerificationKey slotVkChunks (F StepField) Boolean
mkVerificationKey r = VerificationKey
  { maxProofsVerified: proofsVerifiedToBoolVec r.maxProofsVerified
  , actualWrapDomainSize: proofsVerifiedToBoolVec r.actualWrapDomainSize
  , wrapIndex: r.wrapIndex
  }
