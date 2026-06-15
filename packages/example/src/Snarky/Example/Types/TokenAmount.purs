module Snarky.Example.Types.TokenAmount
  ( TokenAmount(..)
  , mkAmount
  , addWithOverflow
  , subWithUnderflow
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe, fromJust)
import Data.Newtype (class Newtype, un)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, add_, assertEqual_, const_, exists, fieldsToValue, fieldsToVar, fromField, read, scale_, sizeInFields, sub_, toField, valueToFields, varToFields)
import Snarky.Circuit.Kimchi.RangeCheck (rangeCheck128)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | TokenAmount type - a single field element representing a token balance
newtype TokenAmount f = TokenAmount (SizedF 128 f)

derive instance Newtype (TokenAmount f) _
derive instance Generic (TokenAmount f) _
derive newtype instance Show f => Show (TokenAmount f)
derive newtype instance WriteForeign f => WriteForeign (TokenAmount f)
derive newtype instance ReadForeign f => ReadForeign (TokenAmount f)
derive newtype instance Eq f => Eq (TokenAmount f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (TokenAmount f)

instance (CircuitType f a var) => CircuitType f (TokenAmount a) (TokenAmount var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @a)
  valueToFields (TokenAmount x) = valueToFields $ toField x
  fieldsToValue fs = TokenAmount (fieldsToValue fs)
  varToFields (TokenAmount x) = varToFields @_ @(SizedF 128 a) x
  fieldsToVar fs = TokenAmount (fieldsToVar @_ @(SizedF 128 a) fs)

-- | Range-check a token balance to 128 bits via the `EndoScalar` gate
-- | instead of bit unpacking. Specialised to `Vesta.ScalarField` — the
-- | only field token amounts ever live in — which lets us pull the endo
-- | coefficient straight from `HasEndo` as a constant.
instance
  CheckedType Vesta.ScalarField
    (KimchiConstraint Vesta.ScalarField)
    (TokenAmount (FVar Vesta.ScalarField)) where
  check (TokenAmount v) = rangeCheck128 (const_ endo) v
    where
    EndoScalar endo = endoScalar @Vesta.BaseField @Vesta.ScalarField

-- | Flatten via the `CircuitType` field representation.
instance Hashable (TokenAmount (F f)) (F f) where
  toHashInput x = map F (valueToFields x)

instance Hashable (TokenAmount (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(TokenAmount (F f))

-- | Add two token balances, detecting 128-bit overflow.
-- |
-- | Both inputs are `< 2^128`, so their field sum is `< 2^129`. We witness
-- | the low 128 bits as `result` and the carry as `overflow`; `exists`
-- | range-checks `result` (via `TokenAmount`'s endo-gate `check`) and
-- | constrains `overflow` to a boolean, and one linear constraint ties the
-- | pieces back to the sum.
addWithOverflow
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  => TokenAmount (FVar f)
  -> TokenAmount (FVar f)
  -> Snarky f (KimchiConstraint f) r
       { result :: TokenAmount (FVar f), overflow :: BoolVar f }
addWithOverflow a b = do
  let sumF = add_ (toField (un TokenAmount a)) (toField (un TokenAmount b))
  Tuple result overflow <- exists do
    F s <- read sumF
    let
      sBig = toBigInt s

      lo :: SizedF 128 (F f)
      lo = unsafePartial $ fromJust $ fromField @128 (fromBigInt (mod sBig two128))
    pure $ Tuple (TokenAmount lo) (sBig >= two128)
  assertEqual_ sumF
    (add_ (toField (un TokenAmount result)) (scale_ (fromBigInt two128) (coerce overflow)))
  pure { result, overflow }
  where
  two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)

-- | Subtract one token balance from another, detecting 128-bit underflow.
-- |
-- | We want `result = a - b + underflow · 2^128`, with `result` in
-- | `[0, 2^128)` and `underflow` a bit: when `a >= b` the borrow is 0 and
-- | `result = a - b`; when `a < b` the borrow is 1 and `result =
-- | a - b + 2^128`. `exists` range-checks `result` and constrains
-- | `underflow` to a boolean, and one linear constraint ties them to the
-- | field difference — which together pin `underflow` to the true borrow.
subWithUnderflow
  :: forall f r
   . PrimeField f
  => FieldSizeInBits f 255
  => CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  => TokenAmount (FVar f)
  -> TokenAmount (FVar f)
  -> Snarky f (KimchiConstraint f) r
       { result :: TokenAmount (FVar f), underflow :: BoolVar f }
subWithUnderflow a b = do
  let
    aF = toField (un TokenAmount a)
    bF = toField (un TokenAmount b)
  Tuple result underflow <- exists do
    F av <- read aF
    F bv <- read bF
    let
      aBig = toBigInt av
      bBig = toBigInt bv
      borrow = aBig < bBig

      lo :: SizedF 128 (F f)
      lo = unsafePartial $ fromJust $ fromField @128
        (fromBigInt (if borrow then aBig - bBig + two128 else aBig - bBig))
    pure $ Tuple (TokenAmount lo) borrow
  assertEqual_ (toField (un TokenAmount result))
    (add_ (sub_ aF bF) (scale_ (fromBigInt two128) (coerce underflow)))
  pure { result, underflow }
  where
  two128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)

mkAmount
  :: forall f m
   . FieldSizeInBits f m
  => Compare 128 m LT
  => f
  -> Maybe (TokenAmount f)
mkAmount f = TokenAmount <$> fromField f