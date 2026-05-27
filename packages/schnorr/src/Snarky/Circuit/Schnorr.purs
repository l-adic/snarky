-- | In-circuit Schnorr signature verifier (kimchi gates).
-- |
-- | This is the kimchi-gate verifier that mirrors `schnorr_verify_circuit`
-- | in `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`. Both signature
-- | components `r` and `s` live in the native circuit field
-- | (`Pallas.BaseField = Vesta.ScalarField`), not in the curve's scalar
-- | field — the verifier interprets `s` and `e` as Tick.Field values that
-- | get cross-field scalar-multiplied via `scaleFast2'`, which adds a
-- | `2^255` shift internally. See `Data.Schnorr.sign` for the matching
-- | signer.
-- |
-- | Constraint shape (verified byte-identical to the OCaml dump via
-- | `packages/pickles-circuit-diffs/circuits/ocaml/schnorr_verify_step_circuit.json`):
-- |   - 22 Poseidon gates  (zero-seed sponge over `pk.x, pk.y, r, msg...`)
-- |   - 102 VarBaseMul gates (two 254-bit `scaleFast2'`)
-- |   - 5 CompleteAdd gates  (one `addFast DontCheckFinite` + four inside scaleFast)
-- |   - 275 Generic + 104 Zero  (boolean + seal + unpack + glue)
-- |
-- | Iteration 1 uses a zero-seed Poseidon sponge. Iteration 2 will
-- | front-load the OCaml `Hash_prefix_states.signature ~signature_kind`
-- | for Mina deployed-Schnorr bit-compat.
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
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, and_, equals_, negate_, not_, unpack_)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2')
import Snarky.Circuit.RandomOracle.Sponge (absorb, initialState, squeeze) as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))
import RandomOracle.Sponge (create) as Sponge

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
-- | boolean. The verifier curve `gen` is the matching curve's generator
-- | as a circuit-constant point.
-- |
-- | Algorithm (matches `schnorr_verify_circuit` byte-for-byte):
-- |   1. `e = Poseidon(pk.x, pk.y, r, ...message)` (zero-seed sponge).
-- |   2. `negPk = (pk.x, -pk.y)`.
-- |   3. `e_pk = scaleFast2' negPk e` (= `[e + 2^255] * (-pk)`).
-- |   4. `s_g  = scaleFast2' gen   s` (= `[s + 2^255] * gen`).
-- |   5. `r_pt = addFast DontCheckFinite s_g e_pk`.
-- |   6. `y_even = LSB of unpack(r_pt.y, ~length:size_in_bits-1) is 0`.
-- |   7. `r_correct = (r_pt.x == r)`.
-- |   8. Accept iff `r_correct && y_even`.
-- |
-- | The pinned `@51 @253` type-application encodes `num_bits=254`:
-- |   - `nChunks = 51`, so `bitsUsed = 5 * 51 = 255` (== matching OCaml
-- |     `actual_bits_used`).
-- |   - `sDiv2Bits = 253`, so the top `255 - 253 = 2` bits of
-- |     `s_div_2` are constrained to zero (mirrors OCaml's
-- |     `for i = s_div_2_bits to ...` zero loop).
verifies
  :: forall t m n
   . Reflectable n Int
  => PoseidonField Pallas.BaseField
  => CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t m
  => AffinePoint (FVar Pallas.BaseField)
  -> VerifyInput n Pallas.BaseField
  -> Snarky (KimchiConstraint Pallas.BaseField) t m (BoolVar Pallas.BaseField)
verifies gen { publicKey: pk, signature: Signature { r, s }, message } = do
  -- 1. Hash e = Poseidon(pk.x, pk.y, r, ...message) via the
  -- `Step_main_inputs.Sponge`-equivalent absorb-each-field-then-squeeze
  -- pattern (so `Util.seal` after each `add_assign` lines up).
  let sponge0 = Sponge.create Sponge.initialState
  sponge1 <- Sponge.absorb pk.x sponge0
  sponge2 <- Sponge.absorb pk.y sponge1
  sponge3 <- Sponge.absorb r sponge2
  spongeN <- foldM (\sp x -> Sponge.absorb x sp) sponge3 (Vector.toUnfoldable message :: Array _)
  { result: e } <- Sponge.squeeze spongeN
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
