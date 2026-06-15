module Snarky.Example.Types.PublicKey
  ( PublicKey(..)
  , toBase58Check
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Safe.Coerce (coerce)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Circuit.DSL (class AssertEqual, class CheckedType, class CircuitType, F(..), FVar, assertEq, check, fieldsToValue, fieldsToVar, isEqual, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Curves.Class (toHexLe)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | PublicKey type - a single field element representing a public key
newtype PublicKey f = PublicKey (AffinePoint f)

derive instance Newtype (PublicKey f) _
derive instance Generic (PublicKey f) _
derive newtype instance Show f => Show (PublicKey f)
derive newtype instance WriteForeign f => WriteForeign (PublicKey f)
derive newtype instance ReadForeign f => ReadForeign (PublicKey f)
derive newtype instance Eq f => Eq (PublicKey f)
derive newtype instance Ord f => Ord (PublicKey f)
derive newtype instance Arbitrary f => Arbitrary (PublicKey f)
derive instance Functor PublicKey

-- | Route through an explicit `Tuple2 (x, y)` so the coordinate layout
-- | is fixed and visible, rather than the record's RowList order.
instance CircuitType f (PublicKey f) (PublicKey (FVar f)) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 (F f) (F f)))
  valueToFields a = case coerce a :: PublicKey (F f) of
    PublicKey (AffinePoint pk) -> valueToFields (tuple2 pk.x pk.y)
  fieldsToValue fs = coerce (uncurry2 (\x y -> PublicKey (AffinePoint { x, y })) (fieldsToValue @_ @(Tuple2 (F f) (F f)) fs) :: PublicKey (F f))
  varToFields (PublicKey (AffinePoint pk)) = varToFields @_ @(Tuple2 (F f) (F f)) (tuple2 pk.x pk.y)
  fieldsToVar fs = uncurry2 (\x y -> PublicKey (AffinePoint { x, y })) (fieldsToVar @_ @(Tuple2 (F f) (F f)) fs)

instance CheckedType f c var => CheckedType f c (PublicKey var) where
  check (PublicKey (AffinePoint pk)) = check (tuple2 pk.x pk.y)

instance AssertEqual f c var => AssertEqual f c (PublicKey var) where
  assertEq (PublicKey (AffinePoint a)) (PublicKey (AffinePoint b)) = assertEq (tuple2 a.x a.y) (tuple2 b.x b.y)
  isEqual (PublicKey (AffinePoint a)) (PublicKey (AffinePoint b)) = isEqual (tuple2 a.x a.y) (tuple2 b.x b.y)

-- | Flatten via the `CircuitType` field representation, so the hash
-- | layout always matches the circuit serialization order.
instance Hashable (PublicKey Vesta.ScalarField) Vesta.ScalarField where
  toHashInput = valueToFields

instance Hashable (PublicKey Pallas.ScalarField) Pallas.ScalarField where
  toHashInput = valueToFields

instance Hashable (PublicKey (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(PublicKey f)

-- | Render a public key as a Mina-style `B62…` address — the
-- | compressed-point base58check form shown by Mina explorers and the
-- | GraphQL API, far more succinct than printing the full affine point.
-- | Byte-faithful to MinaProtocol/mina's `non_zero_curve_point`
-- | compressed encoding (validated against real network addresses).
toBase58Check :: PublicKey Vesta.ScalarField -> String
toBase58Check (PublicKey (AffinePoint { x, y })) = pubkeyToBase58 (toHexLe x) (toHexLe y)

-- | base58check encode the compressed key from the little-endian hex of
-- | its affine coordinates (the parity bit is read from `y`).
foreign import pubkeyToBase58 :: String -> String -> String
