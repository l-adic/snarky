-- | Circuit implementation of Schnorr signature verification.
-- |
-- | This module provides the circuit (constraint-system) implementation
-- | of Schnorr signature verification for use in zero-knowledge proofs.
-- |
-- | In circuits, both signature components (r and s) are represented as
-- | elements of the native circuit field, even though mathematically they
-- | may come from different fields (base vs scalar).
module Snarky.Circuit.Schnorr
  ( SignatureVar(..)
  , sigR
  , sigS
  , isEven
  , hashMessage
  , verifies
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
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, not_, unpack_)
import Snarky.Circuit.DSL.Field (equals_)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2, splitFieldVar)
import Snarky.Circuit.RandomOracle (Digest(..), hashVec)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type2)

-- | Circuit variable type for Schnorr signatures.
-- | r is the x-coordinate of R (circuit field element).
-- | s is a scalar field element represented as Type2 (for foreign field case).
newtype SignatureVar f = SignatureVar
  { r :: FVar f
  , s :: Type2 (FVar f) (BoolVar f)
  }

derive instance Newtype (SignatureVar f) _
derive instance Generic (SignatureVar f) _

-- | Extract the r component from a SignatureVar.
sigR :: forall f. SignatureVar f -> FVar f
sigR (SignatureVar { r }) = r

-- | Extract the s component from a SignatureVar.
sigS :: forall f. SignatureVar f -> Type2 (FVar f) (BoolVar f)
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
verifies
  :: forall f t m n l @nChunks sDiv2Bits bitsUsed _l
   . PoseidonField f
  => Reflectable l Int
  => FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> { signature :: SignatureVar f
     , publicKey :: AffinePoint (FVar f)
     , message :: Vector l (FVar f)
     }
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
verifies gen { signature: SignatureVar { r, s }, publicKey, message } = do
  Digest e <- hashMessage @l publicKey r message
  eSplit <- splitFieldVar e
  sG <- scaleFast2 @nChunks gen s
  ePk <- scaleFast2 @nChunks publicKey eSplit
  negEPk <- EllipticCurve.negate ePk
  { p: rPoint } <- addComplete sG negEPk
  isEven rPoint.y && equals_ rPoint.x r