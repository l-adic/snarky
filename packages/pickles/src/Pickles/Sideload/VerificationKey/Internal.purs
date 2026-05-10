-- | Internal module for `Pickles.Sideload.VerificationKey`. Exposes
-- | the data constructor + the compile-time placeholder for library
-- | code that needs them. User code should import the facade
-- | `Pickles.Sideload.VerificationKey` instead.
module Pickles.Sideload.VerificationKey.Internal
  ( ProofsVerified(..)
  , ProofsVerifiedCount
  , boolVecToProofsVerified
  , Checked(..)
  , SideloadedVK(..)
  , VerificationKey
  , CompilePlaceholderVK
  , VerificationKeyVar
  , compileDummy
  , cellCircuit
  , fromCompiledWrap
  ) where

import Prelude

import Data.Enum (class BoundedEnum, class Enum)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.ProofFFI (vestaVerifierIndexCommitments)
import Pickles.Types (StepField, WrapField)
import Pickles.Types (VerificationKey(..)) as PT
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, assertExactlyOne_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Number of proofs a Pickles VK verifies; capped at 2 for the
-- | side-loaded protocol (`Width.Max = Nat.N2`).
data ProofsVerified = N0 | N1 | N2

-- | Type-level cardinality of `ProofsVerified` (= 3 for {N0, N1, N2}).
-- | Used to size one-hot bool vectors and per-domain lookup tables
-- | indexed by a side-loaded VK's `actualWrapDomainSize`.
type ProofsVerifiedCount = 3

derive instance Eq ProofsVerified
derive instance Ord ProofsVerified
derive instance Generic ProofsVerified _

instance Show ProofsVerified where
  show = genericShow

instance Bounded ProofsVerified where
  bottom = N0
  top = N2

instance Enum ProofsVerified where
  succ = genericSucc
  pred = genericPred

instance BoundedEnum ProofsVerified where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

-- | Boolean-form one-hot vector.
proofsVerifiedToBoolVec :: ProofsVerified -> Vector ProofsVerifiedCount Boolean
proofsVerifiedToBoolVec = case _ of
  N0 -> true :< false :< false :< Vector.nil
  N1 -> false :< true :< false :< Vector.nil
  N2 -> false :< false :< true :< Vector.nil

-- | Circuit-shape record carrying the three Typ-relevant fields of a
-- | side-loaded VK, in OCaml hlist order
-- | `[ max_proofs_verified ; actual_wrap_domain_size ; wrap_index ]`.
-- |
-- | Parameterised on `b` (Boolean / BoolVar) and `pt` (concrete /
-- | circuit-var curve point) so the same record carries both forms.
newtype Checked b pt = Checked
  { maxProofsVerified :: Vector 3 b
  , actualWrapDomainSize :: Vector 3 b
  , wrapIndex :: PT.VerificationKey pt
  }

derive instance Generic (Checked b pt) _

instance
  ( CircuitType f b bvar
  , CircuitType f pt ptvar
  ) =>
  CircuitType f (Checked b pt) (Checked bvar ptvar) where
  sizeInFields pf _ =
    genericSizeInFields pf
      (Proxy @(Tuple3 (Vector 3 b) (Vector 3 b) (PT.VerificationKey pt)))
  valueToFields (Checked r) =
    genericValueToFields (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 3 b) (Vector 3 b) (PT.VerificationKey pt)
      tup = genericFieldsToValue fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            Checked { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup
  varToFields (Checked r) =
    genericVarToFields
      @(Tuple3 (Vector 3 b) (Vector 3 b) (PT.VerificationKey pt))
      (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 3 bvar) (Vector 3 bvar) (PT.VerificationKey ptvar)
      tup = genericFieldsToVar
        @(Tuple3 (Vector 3 b) (Vector 3 b) (PT.VerificationKey pt))
        fs
    in
      uncurry3
        ( \maxProofsVerified actualWrapDomainSize wrapIndex ->
            Checked { maxProofsVerified, actualWrapDomainSize, wrapIndex }
        )
        tup

-- | `CheckedType` for the var form. Each one-hot field gets boolean
-- | checks immediately followed by `assertExactlyOne` (matching OCaml
-- | `One_hot.typ`'s emission order); `wrap_index` runs its on-curve
-- | checks last.
instance
  ( CheckedType f c ptvar
  , CheckedType f c (BoolVar f)
  , PrimeField f
  ) =>
  CheckedType f c (Checked (BoolVar f) ptvar) where
  check (Checked r) = do
    label "vk_max_proofs_verified" do
      label "boolean_checks" $ check r.maxProofsVerified
      label "exactly_one"
        $ assertExactlyOne_ (Vector.toUnfoldable r.maxProofsVerified)
    label "vk_actual_wrap_domain_size" do
      label "boolean_checks" $ check r.actualWrapDomainSize
      label "exactly_one"
        $ assertExactlyOne_ (Vector.toUnfoldable r.actualWrapDomainSize)
    label "vk_wrap_index" $ check r.wrapIndex

-- | In-circuit form of a side-loaded VK.
type VerificationKeyVar f =
  Checked (BoolVar f) (WeierstrassAffinePoint Pallas.G (FVar f))

-- | Side-loaded VK bundle parameterised by the runtime payload type.
-- |
-- | * `circuit` — in-circuit `Checked` shape; always present (allocated
-- |   into the step circuit by `traverseSideloadedVKsCarrier`).
-- | * `wrapVk` — payload. At prove time this is a hydrated kimchi
-- |   `VerifierIndex`; at compile time it is `Unit` (the compile-time
-- |   placeholder needs no runtime VK because the constraint-system
-- |   pass never reads it).
-- |
-- | Use the type aliases `VerificationKey` / `CompilePlaceholderVK`
-- | for the two phases — they are interchangeable with `SideloadedVK …`
-- | wherever PS expects a saturated type.
newtype SideloadedVK a = SideloadedVK
  { circuit :: Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))
  , wrapVk :: a
  }

-- | Prove-time alias: payload is a hydrated kimchi `VerifierIndex`.
-- | Smart constructors `loadVerificationKey` / `fromCompiledWrap`
-- | produce values of this type and guarantee the payload is real.
type VerificationKey = SideloadedVK (VerifierIndex Pallas.G WrapField)

-- | Compile-time alias: payload is `Unit`. Synthesised by
-- | `Pickles.Sideload.Advice.MkUnitVkCarrier` for the
-- | constraint-system pass; cannot be passed where a hydrated
-- | `VerifierIndex` is required because `unwrapVerificationKey` is
-- | typed only at the prove-time alias.
type CompilePlaceholderVK = SideloadedVK Unit

-- | Module-level compile-time placeholder. Pure construction — the
-- | `Unit` payload needs no FFI.
-- |
-- | `maxProofsVerified` and `actualWrapDomainSize` are pinned at `N2`
-- | because the placeholder must produce the constraint system shape
-- | of the LARGEST possible side-loaded VK; smaller-mpv runtime VKs
-- | mask down via their own `actualWrapDomainSize` one-hot bits.
compileDummy :: CompilePlaceholderVK
compileDummy = SideloadedVK
  { circuit: mkChecked
      { maxProofsVerified: N2
      , actualWrapDomainSize: N2
      , wrapIndex:
          PT.VerificationKey
            { sigma: Vector.replicate g
            , coeff: Vector.replicate g
            , index: Vector.replicate g
            }
      }
  , wrapVk: unit
  }
  where
  g :: WeierstrassAffinePoint Pallas.G (F StepField)
  g = WeierstrassAffinePoint { x: F zero, y: F zero }

-- | Polymorphic in payload — extracts the in-circuit `Checked` shape
-- | from any `SideloadedVK`. No class machinery needed; it's just
-- | record-field access.
cellCircuit
  :: forall a
   . SideloadedVK a
  -> Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))
cellCircuit (SideloadedVK r) = r.circuit

-- | Build the `circuit` part from the user-friendly `ProofsVerified`
-- | enum for the two one-hot fields.
mkChecked
  :: { maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     , wrapIndex :: PT.VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField))
     }
  -> Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))
mkChecked r = Checked
  { maxProofsVerified: proofsVerifiedToBoolVec r.maxProofsVerified
  , actualWrapDomainSize: proofsVerifiedToBoolVec r.actualWrapDomainSize
  , wrapIndex: r.wrapIndex
  }

-- | Build a side-loaded VK from a PS-side compiled child's wrap
-- | result. `verifierIndex` is the `WrapCompileResult.verifierIndex`
-- | field; it is already a hydrated kimchi handle.
fromCompiledWrap
  :: { verifierIndex :: VerifierIndex Pallas.G WrapField
     , maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     }
  -> VerificationKey
fromCompiledWrap r = SideloadedVK
  { circuit: mkChecked
      { maxProofsVerified: r.maxProofsVerified
      , actualWrapDomainSize: r.actualWrapDomainSize
      , wrapIndex: extractWrapVKComms r.verifierIndex
      }
  , wrapVk: r.verifierIndex
  }

-- | Extract the `Plonk_verification_key_evals.t` shape from a kimchi
-- | wrap `VerifierIndex`. Sigma/coefficient/index commitments only.
extractWrapVKComms
  :: VerifierIndex Pallas.G WrapField
  -> PT.VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField))
extractWrapVKComms vk =
  let
    comms = vestaVerifierIndexCommitments vk

    wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint Pallas.G (F StepField)
    wrapPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    PT.VerificationKey
      { sigma: map wrapPt comms.sigma
      , coeff: map wrapPt comms.coeff
      , index: map wrapPt comms.index
      }

-- | Inverse of `proofsVerifiedToBoolVec`. Defaults to `N0` for the
-- | zero-bit input and for malformed (non-one-hot) inputs.
boolVecToProofsVerified :: Vector 3 Boolean -> ProofsVerified
boolVecToProofsVerified v =
  let
    { head: b0, tail: t1 } = Vector.uncons v
    { head: b1, tail: t2 } = Vector.uncons t1
    { head: b2 } = Vector.uncons t2
  in
    if b0 then N0 else if b1 then N1 else if b2 then N2 else N0

