-- | In-circuit Schnorr signature verifier (kimchi gates).
-- |
-- | Mirrors `schnorr_verify_circuit` in `mina/src/lib/crypto/pickles/
-- | dump_circuit_impl.ml`. Both signature components `r` and `s` live
-- | in the native circuit field (`Pallas.BaseField = Vesta.ScalarField`),
-- | not in the curve's scalar field — the verifier interprets `s` and
-- | `e` as Tick.Field values that get cross-field scalar-multiplied
-- | via `scaleFast2'`, which adds a `2^255` shift internally. See
-- | `Data.Schnorr.sign` for the matching signer.
-- |
-- | The hash uses a caller-supplied 3-element sponge prefix state and
-- | Mina's `Schnorr.Chunked` absorption order: message field-elements
-- | first, then `pk.x`, `pk.y`, `r` (= `Random_oracle.Input.Chunked.append
-- | message {pk; r}`). Callers that want a Mina-deployed prefix can
-- | pass `Data.Schnorr.ChainId.signaturePrefix` of the matching chain;
-- | a zero-prefix is fine for ad-hoc / test-only use cases.
-- |
-- | The IPA-bound rejection (e < 2^254, s < 2^254) and the odd-y
-- | rejection still live in the signer — those depend on the
-- | scalar-mul gate shape and are addressed in iteration 2c (full-range
-- | scalar mul).
module Snarky.Circuit.Schnorr
  ( Signature(..)
  , VerifyInput
  , verifies
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (SpongeState(..))
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, and_, equals_, negate_, not_, unpack_)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Circuit.RandomOracle.Sponge (absorb, spongeFromConstants, squeeze) as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Schnorr signature variables in-circuit. Both `r` and `s` are
-- | native-field variables (`Pallas.BaseField`).
newtype Signature f = Signature
  { r :: FVar f
  , s :: FVar f
  }

derive instance Newtype (Signature f) _
derive instance Generic (Signature f) _

-- | Inputs the verifier consumes — bundled so the circuit-diff
-- | fixture's flattened layout (pk_x, pk_y, r, s, msg…) is the only
-- | place the field order is hard-coded.
type VerifyInput n f =
  { publicKey :: AffinePoint (FVar f)
  , signature :: Signature f
  , message :: Vector n (FVar f)
  }

-- | Verify a Schnorr signature in the circuit, returning the accept
-- | boolean.
-- |
-- | Algorithm (matches Mina's `Schnorr.Chunked.Checked.verifier`
-- | byte-for-byte at the hash level when `spongePrefix` is set to the
-- | Mina `Hash_prefix_states.signature` of the matching chain; scalar
-- | mul shape differs — see module header):
-- |   1. `e = Poseidon(message…, pk.x, pk.y, r)` seeded with `spongePrefix`.
-- |   2. `negPk = (pk.x, -pk.y)`.
-- |   3. `e_pk = scaleFast2' negPk e` (= `[e + 2^255] * (-pk)`).
-- |   4. `s_g  = scaleFast2' gen   s` (= `[s + 2^255] * gen`).
-- |   5. `r_pt = addFast DontCheckFinite s_g e_pk`.
-- |   6. `y_even = LSB of unpack(r_pt.y, ~length:size_in_bits-1) is 0`.
-- |   7. `r_correct = (r_pt.x == r)`.
-- |   8. Accept iff `r_correct && y_even`.
verifies
  :: forall t m n
   . Reflectable n Int
  => PoseidonField Pallas.BaseField
  => CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t m
  => Vector 3 Pallas.BaseField
  -> AffinePoint (FVar Pallas.BaseField)
  -> VerifyInput n Pallas.BaseField
  -> Snarky (KimchiConstraint Pallas.BaseField) t m (BoolVar Pallas.BaseField)
verifies spongePrefix gen { publicKey: pk, signature: Signature { r, s }, message } = do
  -- 1. Hash via `Schnorr.Chunked.Message.hash`: prefix-state-seeded
  -- sponge, absorb the `Input.Chunked.append message {pk; r}` field
  -- sequence (message first), squeeze.
  let
    sponge0 = Sponge.spongeFromConstants
      { state: spongePrefix
      , spongeState: Squeezed (unsafeFinite 0)
      }
  spongeMsg <- foldM (\sp x -> Sponge.absorb x sp)
    sponge0
    (Vector.toUnfoldable message :: Array _)
  sponge1 <- Sponge.absorb pk.x spongeMsg
  sponge2 <- Sponge.absorb pk.y sponge1
  sponge3 <- Sponge.absorb r sponge2
  { result: e } <- Sponge.squeeze sponge3
  -- 2. neg_pk: snarky_curve's negate is `(x, -y)`, no constraint.
  let negPk = { x: pk.x, y: negate_ pk.y }
  -- 3-4. Two scaleFast2' calls with num_bits=254.
  ePk <- scaleFast2' @51 @253 negPk e
  sG <- scaleFast2' @51 @253 gen s
  -- 5. r_pt = s_g + e_pk via add_fast ~check_finite:false.
  { p: rPt } <- addFast DontCheckFinite sG ePk
  -- 6. y_even: head of unpacked y bits (LSB) must be 0.
  yBits <- unpack_ rPt.y (Proxy @254)
  let yEven = not_ (Vector.index yBits (unsafeFinite 0))
  -- 7. r_correct = (r_pt.x == r).
  rCorrect <- equals_ rPt.x r
  -- 8. accept.
  and_ rCorrect yEven
