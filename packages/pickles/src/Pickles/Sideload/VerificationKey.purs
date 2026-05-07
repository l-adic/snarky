-- | Data model and `Typ` for Pickles side-loaded verification keys: the
-- | wrap-proof verification key supplied at runtime rather than baked
-- | into compile output, used inside a step circuit to verify a
-- | side-loaded child's wrap proof.
-- |
-- | Reference: OCaml `Pickles.Side_loaded.Verification_key`.
module Pickles.Sideload.VerificationKey
  ( ProofsVerified(..)
  , proofsVerifiedToOneHotValue
  , proofsVerifiedToBoolVec
  , boolVecToProofsVerified
  , Checked(..)
  , VerificationKey
  , VerificationKeyVar
  , mkChecked
  , dummy
  , toInputValue
  , toInputVar
  ) where

import Prelude

import Data.Enum (class BoundedEnum, class Enum)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Types (StepField, WrapField)
import Pickles.Types (VerificationKey(..)) as PT
import RandomOracle.Input (Chunked)
import RandomOracle.Input as RO
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, assertExactlyOne_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Number of proofs a Pickles VK verifies; capped at 2 for the
-- | side-loaded protocol (`Width.Max = Nat.N2`).
data ProofsVerified = N0 | N1 | N2

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

-- | One-hot field-element encoding:
-- | `N0 → [1,0,0]`, `N1 → [0,1,0]`, `N2 → [0,0,1]`.
proofsVerifiedToOneHotValue
  :: forall f. PrimeField f => ProofsVerified -> Vector 3 f
proofsVerifiedToOneHotValue = case _ of
  N0 -> one :< zero :< zero :< Vector.nil
  N1 -> zero :< one :< zero :< Vector.nil
  N2 -> zero :< zero :< one :< Vector.nil

-- | Boolean-form one-hot vector.
proofsVerifiedToBoolVec :: ProofsVerified -> Vector 3 Boolean
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

-- | In-circuit form of a side-loaded VK. Pallas inner-curve, step
-- | circuit's host field. Allocated via
-- | `exists @(VerificationKeyVar f) ~compute:(\_ -> toChecked vk)`.
type VerificationKeyVar f =
  Checked (BoolVar f) (WeierstrassAffinePoint Pallas.G (FVar f))

-- | Concrete (prover-side) side-loaded verification key.
-- |
-- | * `circuit` — the circuit-relevant data in `Checked` form;
-- |   allocated as a `VerificationKeyVar` via `exists`.
-- | * `wrapVk` — runtime kimchi `VerifierIndex` for the side-loaded
-- |   child's wrap proof. FFI handle (not field-encodable), kept out
-- |   of the circuit-marshalled side. Consumed by the verify path
-- |   and by `mkStepAdvice` for `vestaProofOracles`. `Nothing` for
-- |   the `dummy` placeholder.
type VerificationKey =
  { circuit :: Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))
  , wrapVk :: Maybe (VerifierIndex Pallas.G WrapField)
  }

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

-- | Sentinel side-loaded VK: `maxProofsVerified = N2`,
-- | `actualWrapDomainSize = N2`, zero curve points for `wrap_index`,
-- | `wrapVk = Nothing`. Reference: OCaml
-- | `side_loaded_verification_key.ml`'s `dummy`.
dummy :: VerificationKey
dummy =
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
  , wrapVk: Nothing
  }
  where
  -- The dummy is only consumed before the real VK is bound, so the
  -- concrete commitment values aren't load-bearing — zero placeholder
  -- avoids pulling in a curve-generator dependency.
  g :: WeierstrassAffinePoint Pallas.G (F StepField)
  g = WeierstrassAffinePoint { x: F zero, y: F zero }

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

-- | Random-oracle input for a value-side VK: 3 packed 1-bit chunks for
-- | each one-hot field, then 56 raw field elements for `wrap_index`
-- | (sigma · coeff · index, two coords per point). `wrapVk` is not
-- | hashed.
toInputValue :: VerificationKey -> Chunked StepField
toInputValue vk =
  let
    Checked r = vk.circuit
  in
    oneHotChunk (boolVecToOneHot r.maxProofsVerified)
      `RO.append` oneHotChunk (boolVecToOneHot r.actualWrapDomainSize)
      `RO.append` wrapIndexInput r.wrapIndex
  where
  boolVecToOneHot :: Vector 3 Boolean -> Vector 3 StepField
  boolVecToOneHot = map (\b -> if b then one else zero)

  oneHotChunk :: Vector 3 StepField -> Chunked StepField
  oneHotChunk v =
    RO.packeds $ map (\b -> { value: b, length: 1 }) (Vector.toUnfoldable v)

  wrapIndexInput
    :: PT.VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField))
    -> Chunked StepField
  wrapIndexInput wi =
    RO.fieldElements $
      valueToFields
        @StepField
        @(PT.VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField)))
        wi

-- | In-circuit version of `toInputValue`. The one-hot bitvec lives as
-- | `BoolVar`s, coerced to `FVar` (single-bit field expressions) for
-- | the packed chunks.
toInputVar
  :: forall f
   . PrimeField f
  => VerificationKeyVar f
  -> Chunked (FVar f)
toInputVar (Checked r) =
  oneHotChunk r.maxProofsVerified
    `RO.append` oneHotChunk r.actualWrapDomainSize
    `RO.append` RO.fieldElements
      (varToFields @f @(PT.VerificationKey (WeierstrassAffinePoint Pallas.G (F f))) r.wrapIndex)
  where
  oneHotChunk :: Vector 3 (BoolVar f) -> Chunked (FVar f)
  oneHotChunk v =
    RO.packeds $
      map (\b -> { value: (coerce b :: FVar f), length: 1 }) (Vector.toUnfoldable v)
