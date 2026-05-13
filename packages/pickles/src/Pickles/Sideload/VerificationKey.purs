-- | Side-loaded VK descriptor: a child's wrap VK at the protocol
-- | level, containing only the data the parent's step circuit walks.
-- |
-- | Two type parameters select between value and var forms via the
-- | same record:
-- |
-- | * value: `VerificationKey (F StepField) Boolean`
-- | * var:   `VerificationKey (FVar f)     (BoolVar f)`
-- |
-- | No kimchi runtime handle here — that lives in
-- | `Pickles.Sideload.Bundle`.
-- |
-- | Reference: OCaml `Pickles.Side_loaded.Verification_key`.
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
import Pickles.VerificationKey as VK
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, assertExactlyOne_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Side-loaded VK at the protocol level. Three Typ-relevant fields in
-- | OCaml hlist order
-- | `[ max_proofs_verified ; actual_wrap_domain_size ; wrap_index ]`:
-- |
-- | * `maxProofsVerified` — the VK's mpv ∈ {N0, N1, N2}, one-hot.
-- |
-- | * `actualWrapDomainSize` — *not* a domain size in the integer
-- |   sense; OCaml's `Side_loaded.Domain.t` reuses
-- |   `Pickles_base.Proofs_verified.t` because side-loaded wrap
-- |   circuits support exactly three domain sizes (2^13, 2^14, 2^15)
-- |   and these correspond 1:1 to mpv ∈ {N0, N1, N2}. So this field
-- |   is "which of the three supported wrap domains is in play",
-- |   tagged by the enum value, not the literal log2.
-- |
-- | Both are stored as one-hot `Vector ProofsVerifiedCount b` because
-- | the in-circuit form has Boolean wires and cannot pattern-match on
-- | an enum.
newtype VerificationKey :: Int -> Type -> Type -> Type
newtype VerificationKey nc f b = VerificationKey
  { maxProofsVerified :: Vector ProofsVerifiedCount b
  , actualWrapDomainSize :: Vector ProofsVerifiedCount b
  , wrapIndex :: VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G f)
  }

derive instance Generic (VerificationKey nc f b) _

-- | Bridges the value saturation `(F g, Boolean)` to the var
-- | saturation `(FVar g, BoolVar g)`. Concrete-headed (rather than
-- | parametric in the row elements) because the inner
-- | `WeierstrassAffinePoint`'s `CircuitType` instance is itself keyed
-- | on `(F f) -> (FVar f)`, not on arbitrary `a -> var`.
instance
  ( PrimeField g
  , Reflectable nc Int
  ) =>
  CircuitType g
    (VerificationKey nc (F g) Boolean)
    (VerificationKey nc (FVar g) (BoolVar g)) where
  sizeInFields pf _ =
    genericSizeInFields pf
      (Proxy @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (F g)))))
  valueToFields (VerificationKey r) =
    genericValueToFields (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (F g)))
      tup = genericFieldsToValue fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            VerificationKey { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup
  varToFields (VerificationKey r) =
    genericVarToFields
      @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (F g))))
      (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector ProofsVerifiedCount (BoolVar g)) (Vector ProofsVerifiedCount (BoolVar g)) (VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (FVar g)))
      tup = genericFieldsToVar
        @(Tuple3 (Vector ProofsVerifiedCount Boolean) (Vector ProofsVerifiedCount Boolean) (VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (F g))))
        fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            VerificationKey { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup

-- | `CheckedType` for the var form. Each one-hot field gets boolean
-- | checks immediately followed by `assertExactlyOne` (matching OCaml
-- | `One_hot.typ`'s emission order); `wrap_index` runs its on-curve
-- | checks last.
instance
  ( CheckedType g c (WeierstrassAffinePoint Pallas.G (FVar g))
  , CheckedType g c (BoolVar g)
  , PrimeField g
  ) =>
  CheckedType g c (VerificationKey nc (FVar g) (BoolVar g)) where
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

-- | Module-level compile-time placeholder sized for the LARGEST
-- | possible side-loaded VK (mpv = N2, wrap_domain = N2); smaller-mpv
-- | runtime VKs mask down via their own `actualWrapDomainSize` one-hot
-- | bits. Pure construction — feeds `exists` for in-circuit allocation
-- | of the placeholder; the constraint-system pass never reads the
-- | point coordinates. Polymorphic on `nc` (the side-loaded slot's
-- | chunks count, Dim 3); the in-circuit shape replicates the
-- | off-curve placeholder `nc` times per commitment slot.
compileDummy
  :: forall nc
   . Reflectable nc Int
  => VerificationKey nc (F StepField) Boolean
compileDummy = mkVerificationKey
  { maxProofsVerified: N2
  , actualWrapDomainSize: N2
  , wrapIndex:
      VK.VerificationKey
        { sigma: Vector.replicate (Vector.replicate g)
        , coeff: Vector.replicate (Vector.replicate g)
        , index: Vector.replicate (Vector.replicate g)
        }
  }
  where
  -- Off-curve placeholder. Mirrors OCaml `Pickles.Side_loaded.dummy`'s
  -- use of `Inner_curve.Constant.zero` for the wrap-VK commitments.
  g :: WeierstrassAffinePoint Pallas.G (F StepField)
  g = WeierstrassAffinePoint { x: F zero, y: F zero }

-- | Smart constructor from the user-friendly `ProofsVerified` enum.
mkVerificationKey
  :: forall nc
   . { maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     , wrapIndex :: VK.VerificationKey nc (WeierstrassAffinePoint Pallas.G (F StepField))
     }
  -> VerificationKey nc (F StepField) Boolean
mkVerificationKey r = VerificationKey
  { maxProofsVerified: proofsVerifiedToBoolVec r.maxProofsVerified
  , actualWrapDomainSize: proofsVerifiedToBoolVec r.actualWrapDomainSize
  , wrapIndex: r.wrapIndex
  }
