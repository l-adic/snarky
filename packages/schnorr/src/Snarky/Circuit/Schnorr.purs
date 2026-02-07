-- | Circuit implementation of Schnorr signature verification.
-- |
-- | This module provides the circuit (constraint-system) implementation
-- | of Schnorr signature verification for use in zero-knowledge proofs.
-- |
-- | In circuits, both signature components (r and s) are represented as
-- | elements of the native circuit field, even though mathematically they
-- | may come from different fields (base vs scalar).
-- |
-- | The verifier is parameterized by `ScalarOps` which provides the operations
-- | for converting field elements to scalars and performing scalar multiplication.
-- | This allows the code to work with different scalar representations.
module Snarky.Circuit.Schnorr
  ( SignatureVar(..)
  , ScalarOps
  , sigR
  , sigS
  , isEven
  , hashMessage
  , verifies
  -- Curve-specific ops
  , pallasScalarOps
  , vestaScalarOps
  ) where

import Prelude

import Data.Array ((:))
import Data.Fin (unsafeFinite)
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Prim.Int (class Mul)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, check, equals_, not_, unpack_)
import Snarky.Circuit.Kimchi (Type1(..), addComplete, scaleFast1, scaleFast2')
import Snarky.Circuit.RandomOracle (Digest(..), hashVec)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Operations for scalar multiplication in circuits.
-- |
-- | This record captures the operations needed for scalar multiplication with
-- | a specific scalar representation. By passing these operations explicitly,
-- | the verifier function can remain generic while supporting different
-- | scalar types (e.g., Type2 for cross-field arithmetic).
-- |
-- | Type parameters:
-- | - f: the circuit field
-- | - c: the constraint type
-- | - scalar: the scalar representation (e.g., Type2 (FVar f) (BoolVar f))
type ScalarOps f c scalar =
  { -- | Convert a field variable to a scalar representation
    toScalar :: forall t m. CircuitM f c t m => FVar f -> Snarky c t m scalar
  -- | Multiply a point by a scalar
  , scalarMul :: forall t m. CircuitM f c t m => AffinePoint (FVar f) -> scalar -> Snarky c t m (AffinePoint (FVar f))
  }

-- | This is the configuration for Pallas circuits where
-- | the scalar field is larger than the circuit field.
-- | Uses scaleFast2' which splits the field element and adds the 2^n shift internally.
pallasScalarOps
  :: forall @nChunks
   . Mul 5 nChunks 255
  => Reflectable nChunks Int
  => ScalarOps Pallas.BaseField (KimchiConstraint Pallas.BaseField) (FVar Pallas.BaseField)
pallasScalarOps =
  { toScalar: pure
  , scalarMul: scaleFast2' @nChunks
  }

-- | ScalarOps for Vesta.BaseField using Type1 and scaleFast1.
-- |
-- | This is the configuration for Vesta circuits where
-- | the scalar field is smaller than the circuit field.
vestaScalarOps
  :: forall @nChunks
   . Mul 5 nChunks 255
  => Reflectable nChunks Int
  => ScalarOps Vesta.BaseField (KimchiConstraint Vesta.BaseField) (Type1 (FVar Vesta.BaseField))
vestaScalarOps =
  { toScalar: \fvar -> do
      let t1 = Type1 fvar
      check t1
      pure t1
  , scalarMul: scaleFast1 @nChunks
  }

-- | Circuit variable type for Schnorr signatures.
-- | r is the x-coordinate of R (circuit field element).
-- | scalar is the representation of the s component (e.g., Type2 for foreign field case).
newtype SignatureVar f scalar = SignatureVar
  { r :: FVar f
  , s :: scalar
  }

derive instance Newtype (SignatureVar f scalar) _
derive instance Generic (SignatureVar f scalar) _

-- | Extract the r component from a SignatureVar.
sigR :: forall f scalar. SignatureVar f scalar -> FVar f
sigR (SignatureVar { r }) = r

-- | Extract the s component from a SignatureVar.
sigS :: forall f scalar. SignatureVar f scalar -> scalar
sigS (SignatureVar { s }) = s

-- | Check if a field element is even (LSB is 0) in a circuit.
isEven
  :: forall f t m n
   . CircuitM f (KimchiConstraint f) t m
  => FieldSizeInBits f n
  => FVar f
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
isEven y = do
  bits <- unpack_ y
  pure $ not_ $ Vector.index bits (unsafeFinite 0)

-- | Hash the message for signature verification in a circuit.
-- | e = H(pk_x, pk_y, r, message)
hashMessage
  :: forall f t m @n
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Reflectable n Int
  => AffinePoint (FVar f)
  -> FVar f
  -> Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
hashMessage { x: px, y: py } r message = do
  let
    inputs = px : py : r : (Vector.toUnfoldable message)
  hashVec inputs

-- | Verify a Schnorr signature in a circuit, returning a boolean.
-- |
-- | Algorithm:
-- | 1. e = H(pk_x, pk_y, r, message)
-- | 2. R' = [s] * G - [e] * pk
-- | 3. Return: y-coordinate of R' is even AND x-coordinate of R' == r
-- |
-- | The ScalarOps parameter provides toScalar and scalarMul operations,
-- | allowing this function to work with different scalar representations.
verifies
  :: forall f t m n l scalar
   . PoseidonField f
  => Reflectable l Int
  => FieldSizeInBits f n
  => CircuitM f (KimchiConstraint f) t m
  => ScalarOps f (KimchiConstraint f) scalar
  -> AffinePoint (FVar f)
  -> { signature :: SignatureVar f scalar
     , publicKey :: AffinePoint (FVar f)
     , message :: Vector l (FVar f)
     }
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
verifies ops gen { signature: SignatureVar { r, s }, publicKey, message } = do
  Digest e <- hashMessage @l publicKey r message
  eScalar <- ops.toScalar e
  sG <- ops.scalarMul gen s
  ePk <- ops.scalarMul publicKey eScalar
  negEPk <- EllipticCurve.negate ePk
  { p: rPoint } <- addComplete sG negEPk
  isEven rPoint.y && equals_ rPoint.x r