-- | Data model + Typ for Pickles side-loaded verification keys.
-- |
-- | The PS analog of OCaml's
-- | `Pickles.Side_loaded.Verification_key` (compile.ml:1020-1047) and
-- | `Pickles_base.Side_loaded_verification_key` (the underlying
-- | `Poly.t` + `to_input`).
-- |
-- | A side-loaded VK is the verification key for the WRAP proof of
-- | another Pickles circuit, supplied at runtime rather than baked
-- | into the compile output. Used inside a STEP circuit to verify a
-- | side-loaded child's wrap proof.
-- |
-- | * Concrete value (`VerificationKey`): produced via
-- |   `vestaVerifierIndexFromSerdeJson` + `vestaHydrateVerifierIndex`,
-- |   plus the Pickles-domain wrapping fields. Carries an extra
-- |   runtime `wrapVk :: Maybe (VerifierIndex …)` consumed by the
-- |   verify path but never by the in-circuit hash.
-- | * Circuit shape (`Checked b pt`): the parameterized newtype that
-- |   the `CircuitType` / `CheckedType` instances target. It is
-- |   parameterised so that the same record carries both the value
-- |   form (`Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))`)
-- |   and the var form (`Checked (BoolVar f) (WeierstrassAffinePoint Pallas.G (FVar f))`),
-- |   following the same idiom as `Pickles.Types.BranchData`.
-- |
-- | The `wrap_index` commitments are Pallas points (Pallas's base
-- | field is Fp = `StepField`), so each commitment is a
-- | `WeierstrassAffinePoint Pallas.G _` over the appropriate field.
-- |
-- | Reference:
-- |   mina/src/lib/crypto/pickles_base/side_loaded_verification_key.ml
-- |   mina/src/lib/crypto/pickles/side_loaded_verification_key.ml
-- |   mina/src/lib/crypto/pickles/compile.ml:1017-1047
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
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, assertExactlyOne_)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- ProofsVerified — three-state nat with one-hot encoding
--------------------------------------------------------------------------------

-- | Number of proofs a Pickles VK verifies. The side-loaded protocol
-- | caps this at 2 (matching `Width.Max = Nat.N2`); the three-state
-- | enum lets the in-circuit one-hot vector cover {N0, N1, N2}.
-- |
-- | Mirrors `Pickles_base.Proofs_verified.t = N0 | N1 | N2`. Use
-- | `fromEnum` / `toEnum` for the OCaml `to_int` / `of_int_exn`
-- | analogs.
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

-- | One-hot vector of length 3 in field-element form:
-- |   N0 → [1, 0, 0]; N1 → [0, 1, 0]; N2 → [0, 0, 1].
-- |
-- | Mirrors OCaml's `Pickles_base.Proofs_verified.One_hot.to_input`
-- | (`pickles_base/proofs_verified.ml:147-157`).
proofsVerifiedToOneHotValue
  :: forall f. PrimeField f => ProofsVerified -> Vector 3 f
proofsVerifiedToOneHotValue = case _ of
  N0 -> one :< zero :< zero :< Vector.nil
  N1 -> zero :< one :< zero :< Vector.nil
  N2 -> zero :< zero :< one :< Vector.nil

-- | Boolean-form one-hot vector (the value-side representation when
-- | bridging to `Checked Boolean _`).
proofsVerifiedToBoolVec :: ProofsVerified -> Vector 3 Boolean
proofsVerifiedToBoolVec = case _ of
  N0 -> true :< false :< false :< Vector.nil
  N1 -> false :< true :< false :< Vector.nil
  N2 -> false :< false :< true :< Vector.nil

--------------------------------------------------------------------------------
-- Checked — the parameterized circuit-shape record
--
-- Carries the three Typ-relevant fields of a side-loaded VK in OCaml
-- hlist order (`side_loaded_verification_key.ml:396-401`):
--   [ max_proofs_verified ; actual_wrap_domain_size ; wrap_index ]
--
-- Parameterized on:
--   * `b`  — the boolean element type (Boolean for value, BoolVar for var)
--   * `pt` — the curve-point element type
--           (WeierstrassAffinePoint g (F f) for value,
--            WeierstrassAffinePoint g (FVar f) for var)
--
-- Following the `Pickles.Types.BranchData` idiom: a single newtype
-- carries both forms, and the CircuitType instance bridges
-- `Checked b pt → Checked bvar ptvar` whenever the inner instances
-- exist. This piggybacks on the existing `Pickles.Types.VerificationKey`
-- newtype's CircuitType for the wrap_index.
--------------------------------------------------------------------------------

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

-- | CheckedType specialized to the side-loaded VK's actual Var form
-- | (`bvar = BoolVar f`). Mirrors OCaml
-- | `Side_loaded_verification_key.Checked.typ` which composes
-- | `One_hot.typ` (= Vector Boolean.typ + Assert.exactly_one) for both
-- | `max_proofs_verified` and `actual_wrap_domain_size`, plus
-- | `Plonk_verification_key_evals.typ` for `wrap_index`.
-- |
-- | The exactly_one constraints emit one R1CS Generic each (sum of
-- | bools = 1) — without these, PS would silently accept non-one-hot
-- | bitvecs.
instance
  ( CheckedType f c ptvar
  , CheckedType f c (BoolVar f)
  , PrimeField f
  ) =>
  CheckedType f c (Checked (BoolVar f) ptvar) where
  check (Checked r) = do
    -- Vector Boolean.typ checks (b² = b for each bit) + wrap_index
    -- on-curve checks via the existing tuple3 traversal.
    check (tuple3 r.maxProofsVerified r.actualWrapDomainSize r.wrapIndex)
    -- Boolean.Assert.exactly_one for each One_hot field
    -- (`one_hot_vector.ml:30-40`).
    assertExactlyOne_ (Vector.toUnfoldable r.maxProofsVerified)
    assertExactlyOne_ (Vector.toUnfoldable r.actualWrapDomainSize)

--------------------------------------------------------------------------------
-- User-facing types
--------------------------------------------------------------------------------

-- | In-circuit form of a side-loaded VK. Pallas inner-curve (= Tick's
-- | inner curve), step circuit's host field. Allocated via
-- | `exists @(VerificationKeyVar f) ~compute:(\_ -> toChecked vk)`.
type VerificationKeyVar f =
  Checked (BoolVar f) (WeierstrassAffinePoint Pallas.G (FVar f))

-- | Concrete (prover-side) side-loaded verification key.
-- |
-- | Bundles two pieces:
-- |
-- |   * `circuit` — the circuit-relevant data already in `Checked`
-- |     form (one-hot bitvecs + `wrapIndex` commitments). This is
-- |     the side that gets allocated as a `VerificationKeyVar` via
-- |     `exists` — the existing parameterized `CircuitType` instance
-- |     on `Checked b pt` covers the marshalling.
-- |
-- |   * `wrapVk` — the runtime kimchi `VerifierIndex` for the
-- |     side-loaded child's wrap proof, produced via
-- |     `vestaVerifierIndexFromSerdeJson` + `vestaHydrateVerifierIndex`
-- |     (see `Pickles.Sideload.FFI`). This is an FFI handle that
-- |     can't be field-element-encoded, so we keep it OUT of the
-- |     circuit-marshalled side. Used by the Pickles verify path and
-- |     by `mkStepAdvice` for `vestaProofOracles` (driving the
-- |     dummy/InductivePrev wrap-side oracles at prove time). May be
-- |     `Nothing` when only the circuit shape is known (e.g. the
-- |     `dummy` placeholder before a real VK is loaded).
-- |
-- | This split mirrors OCaml's
-- | `Side_loaded.Verification_key.t` semantics: the `Typ.t` only
-- | marshals the Checked shape (`value_to_hlist` drops `wrap_vk`).
-- | We model that explicitly here — `circuit` and `wrapVk` are
-- | independent fields, no asymmetric `CircuitType` instance needed.
type VerificationKey =
  { circuit :: Checked Boolean (WeierstrassAffinePoint Pallas.G (F StepField))
  , wrapVk :: Maybe (VerifierIndex Pallas.G WrapField)
  }

-- | Convenience constructor for the `circuit` part: take the
-- | user-friendly `ProofsVerified` ADT for the two one-hot fields
-- | and produce the `Checked` shape with bool-vec encoding. The
-- | wrap-index commitments pass through unchanged.
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

-- | The dummy side-loaded VK. Mirrors `dummy` in
-- | `mina/src/lib/crypto/pickles/side_loaded_verification_key.ml:330-345`:
-- | `max_proofs_verified = N2`, `actual_wrap_domain_size = N2`,
-- | `wrap_index` filled with the curve generator, `wrap_vk = None`.
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
  -- The OCaml dummy populates wrap_index with `Backend.Tock.Curve.one`'s
  -- affine coordinates; Tock = Pallas, so this is the Pallas generator.
  -- The exact numerical values aren't load-bearing for use as a sentinel
  -- (the dummy is only consumed before the real VK is bound), so we use
  -- a zero placeholder to avoid pulling in a curve-generator dependency.
  g :: WeierstrassAffinePoint Pallas.G (F StepField)
  g = WeierstrassAffinePoint { x: F zero, y: F zero }

-- | Inverse of `proofsVerifiedToBoolVec`. Reads a length-3 one-hot
-- | bit vector and returns the corresponding `ProofsVerified`.
-- |
-- | Defaults to `N0` for the zero-bit input and for malformed
-- | (non-one-hot) inputs. Callers that need strict validation
-- | should check the input themselves; in normal use the input
-- | always comes from a `proofsVerifiedToBoolVec` round-trip and is
-- | well-formed.
boolVecToProofsVerified :: Vector 3 Boolean -> ProofsVerified
boolVecToProofsVerified v =
  let
    { head: b0, tail: t1 } = Vector.uncons v
    { head: b1, tail: t2 } = Vector.uncons t1
    { head: b2 } = Vector.uncons t2
  in
    if b0 then N0 else if b1 then N1 else if b2 then N2 else N0

--------------------------------------------------------------------------------
-- to_input — the random-oracle input for hashing the side-loaded VK
--
-- Mirrors `Pickles_base.Side_loaded_verification_key.to_input`
-- (`pickles_base/side_loaded_verification_key.ml:183-200`):
--   one_hot(max_proofs_verified)        -- 3 packed 1-bit chunks
--   ++ one_hot(actual_wrap_domain_size) -- 3 packed 1-bit chunks
--   ++ field_elements(wrap_index)       -- 56 raw field elements
--------------------------------------------------------------------------------

-- | Build the random-oracle input for a value-side VK. Operates on
-- | the bundle's `circuit` part — `wrapVk` is irrelevant to the hash
-- | (it's an FFI handle, not field-element-encodable).
toInputValue :: VerificationKey -> Chunked StepField
toInputValue vk =
  let Checked r = vk.circuit in
  oneHotChunk (boolVecToOneHot r.maxProofsVerified)
    `RO.append` oneHotChunk (boolVecToOneHot r.actualWrapDomainSize)
    `RO.append` wrapIndexInput r.wrapIndex
  where
  -- Convert a length-3 Boolean one-hot vec to its StepField
  -- representation (true → one, false → zero).
  boolVecToOneHot :: Vector 3 Boolean -> Vector 3 StepField
  boolVecToOneHot = map (\b -> if b then one else zero)

  oneHotChunk :: Vector 3 StepField -> Chunked StepField
  oneHotChunk v =
    RO.packeds $ map (\b -> { value: b, length: 1 }) (Vector.toUnfoldable v)

  -- For the value-side `wrap_index`, the inner element is
  -- `WeierstrassAffinePoint Pallas.G (F StepField)`; flatten via the
  -- existing CircuitType instance (which orders sigma · coeff · index
  -- and emits `[x, y]` per point, already unwrapping each `F`).
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
-- | `BoolVar`s; we coerce to `FVar` (single-bit field expressions) for
-- | the packed chunks. The wrap_index var-side flatten goes through
-- | `varToFields` on `PT.VerificationKey`'s instance.
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
