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
  , mkSignatureVar
  , sigR
  , sigS
  , isEven
  , hashMessage
  , verifies
  , assertVerifies
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, and_, assert_, not_, unpack_)
import Snarky.Circuit.DSL.Field (equals_)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2)
import Snarky.Circuit.RandomOracle (Digest(..), hashVec)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Circuit variable type for Schnorr signatures.
-- | Both r and s are represented as field elements in the circuit.
newtype SignatureVar f = SignatureVar
  { r :: FVar f
  , s :: FVar f
  }

derive instance Newtype (SignatureVar f) _
derive instance Generic (SignatureVar f) _

-- | Create a SignatureVar from individual field variables.
mkSignatureVar :: forall f. FVar f -> FVar f -> SignatureVar f
mkSignatureVar r s = SignatureVar { r, s }

-- | Extract the r component from a SignatureVar.
sigR :: forall f. SignatureVar f -> FVar f
sigR (SignatureVar { r }) = r

-- | Extract the s component from a SignatureVar.
sigS :: forall f. SignatureVar f -> FVar f
sigS (SignatureVar { s }) = s

-- | Check if a field element is even (LSB is 0) in a circuit.
-- | Returns a BoolVar that is true if the field element is even.
isEven
  :: forall f t m n
   . CircuitM f (KimchiConstraint f) t m
  => FieldSizeInBits f n
  => FVar f
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
isEven y = do
  -- Unpack to get the bits (LSB first)
  bits <- unpack_ y
  -- The first bit is the LSB; even if LSB == 0
  let lsb = Vector.index bits (unsafeFinite 0)
  -- Return NOT lsb (true if even)
  pure $ not_ lsb

-- | Hash the message for signature verification in a circuit.
-- |
-- | e = H(pk_x, pk_y, r, H(message))
-- |
-- | This version takes a pre-hashed message digest for simplicity.
hashMessage
  :: forall f t m @n _k
   . PoseidonField f
  => Add 3 n _k
  => Reflectable _k Int
  => CircuitM f (KimchiConstraint f) t m
  => Reflectable n Int
  => AffinePoint (FVar f)
  -> FVar f
  -> Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
hashMessage { x: px, y: py } r message = do
  let
    as = px :< py :< r :< Vector.nil
    inputs = as `Vector.append` message
  hashVec @_k inputs

-- | Verify a Schnorr signature in a circuit, returning a boolean.
-- |
-- | Algorithm:
-- | 1. e = H(pk_x, pk_y, r, H(message))
-- | 2. R' = [s] * G - [e] * pk
-- | 3. Return: y-coordinate of R' is even AND x-coordinate of R' == r
verifies
  :: forall f t m n l @nChunks sDiv2Bits bitsUsed _l _k
   . PoseidonField f
  => Add 3 l _k
  => Reflectable _k Int
  => Reflectable l Int
  => FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> SignatureVar f
  -> AffinePoint (FVar f)
  -> Vector l (FVar f)
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
verifies gen (SignatureVar { r, s }) publicKey message = do
  -- Step 1: Compute challenge hash e = H(pk_x, pk_y, r, H(message))
  Digest e <- hashMessage @l publicKey r message

  -- Step 2: Compute R' = [s] * G - [e] * pk
  -- First compute s*G
  sG <- scaleFast2 @nChunks gen s
  -- Then compute e*pk
  ePk <- scaleFast2 @nChunks publicKey e
  -- Negate e*pk to get -e*pk
  negEPk <- EllipticCurve.negate ePk
  -- Add s*G + (-e*pk) to get R'
  { p: rPoint } <- addComplete sG negEPk

  -- Step 3: Check that y-coordinate of R' is even AND x-coordinate equals r
  yIsEven <- isEven rPoint.y
  xEqualsR <- equals_ rPoint.x r

  and_ yIsEven xEqualsR

-- | Assert that a Schnorr signature is valid in a circuit.
-- |
-- | This is like `verifies` but asserts the result rather than returning it.
assertVerifies
  :: forall f t m n @nChunks sDiv2Bits bitsUsed _l _k
   . PoseidonField f
  => Add 3 n _k
  => Reflectable _k Int
  => FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits 1 n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> SignatureVar f
  -> AffinePoint (FVar f)
  -> Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
assertVerifies gen sig publicKey message = do
  result <- verifies @nChunks gen sig publicKey message
  assert_ result
