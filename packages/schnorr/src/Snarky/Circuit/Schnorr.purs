-- | In-circuit Schnorr signature verifier — first-order port of
-- | `Signature_lib.Schnorr.Make.Checked.verifier`
-- | (`mina/src/lib/crypto/signature_lib/schnorr.ml:271-292`).
-- |
-- | The signature is `(r :: Field, s :: 255-bit scalar)`, matching
-- | production `Signature.var = Field.Var.t * Curve.Scalar.var`
-- | where `Curve.Scalar.var = Boolean.var Bitstring.Lsb_first.t`
-- | (a 255-bool list). `r` is the x-coordinate of the commitment
-- | (a base-field value); `s` is the Pallas scalar transported as
-- | its LSB-first bit decomposition.
-- |
-- | Algorithm:
-- |
-- |   1. `e_bits = Poseidon(message…, pk.x, pk.y, r) → unpack 255 bits`
-- |      seeded with `spongePrefix`.
-- |   2. `shifted = Shifted.create()`.
-- |   3. `e_pk = scale shifted (-pk) e_bits init=Shifted.zero`
-- |      (= `shift + e * (-pk)` in the shifted representation).
-- |   4. `s_g_e_pk = scale shifted G s_bits init=e_pk`
-- |      (= `shift + s * G + e * (-pk)`).
-- |   5. `(rx, ry) = Shifted.unshiftNonzero s_g_e_pk` (= `s*G - e*pk`).
-- |   6. `y_even = LSB(unpack ry) == 0`.
-- |   7. `r_correct = (rx == r)`.
-- |   8. Accept iff both.
-- |
-- | Defers `scale_known` (production uses it for `s*G`); we use plain
-- | `scale` for both bases. Convergence loop will close that gap.
module Snarky.Circuit.Schnorr
  ( Signature(..)
  , VerifyInput
  , pallasParams
  , shiftConst
  , verifies
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (SpongeState(..))
import Snarky.Circuit.DSL (BoolVar, FVar, Snarky, and_, equals_, negate_, not_, unpack_)
import Snarky.Circuit.RandomOracle.Sponge (absorb, spongeFromConstants, squeeze) as Sponge
import Snarky.Circuit.Schnorr.Shifted (ShiftedOps, scale, scaleKnown)
import Snarky.Circuit.Schnorr.UnpackFull (unpackFull)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, curveParams, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..), CurveParams)
import Type.Proxy (Proxy(..))

-- | Schnorr signature in-circuit. `r` is `R.x` (Pallas base-field).
-- | `s` is the Pallas scalar carried as its 255-bit LSB-first
-- | decomposition — same shape as production
-- | `Signature.var = Field.Var.t * Curve.Scalar.var`.
newtype Signature f b = Signature
  { r :: FVar f
  , s :: Vector 255 b
  }

derive instance Newtype (Signature f b) _
derive instance Generic (Signature f b) _

-- | Inputs the verifier consumes — bundled so the public-input
-- | flattening (pk_x, pk_y, r, s_bits[0..254], msg…) is the only
-- | place the order is hard-coded.
type VerifyInput f =
  { publicKey :: AffinePoint (FVar f)
  , signature :: Signature f (BoolVar f)
  , message :: Array (FVar f)
  }

-- | Pallas curve params (a=0, b=5) for `double` inside `scale`.
pallasParams :: CurveParams Pallas.BaseField
pallasParams = curveParams (Proxy :: Proxy PallasG)

-- | The shift point fed to `Shifted.create`. OCaml uses
-- | `Curve.random ()`; we use a constant. CS shape is identical
-- | either way (the shift is `exists`-allocated; its witness value
-- | doesn't enter any constraint).
shiftConst :: AffinePoint Pallas.BaseField
shiftConst =
  let
    g = generator :: PallasG
  in
    AffinePoint (unsafePartial fromJust $ toAffine (g <> g))

-- | Verify a Schnorr signature in the circuit, returning the accept
-- | boolean.
-- |
-- | The `s*G` term uses `scaleKnown` against the curve generator
-- | (`generator :: PallasG` from `WeierstrassCurve`), matching production
-- | `Curve.Checked.scale_known shifted Curve.one s_bits`.
verifies
  :: forall r
   . PoseidonField Pallas.BaseField
  => PrimeField Pallas.BaseField
  => Vector 3 Pallas.BaseField
  -> ShiftedOps Pallas.BaseField r
  -> VerifyInput Pallas.BaseField
  -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) r (BoolVar Pallas.BaseField)
verifies spongePrefix shifted { publicKey: AffinePoint pk, signature: Signature { r, s: sBits }, message } = do
  -- 1. e = Poseidon(message…, pk.x, pk.y, r) seeded with spongePrefix.
  let
    sponge0 = Sponge.spongeFromConstants
      { state: spongePrefix
      , spongeState: Squeezed (unsafeFinite 0)
      }
  spongeMsg <- foldM (\sp x -> Sponge.absorb x sp) sponge0 message
  sponge1 <- Sponge.absorb pk.x spongeMsg
  sponge2 <- Sponge.absorb pk.y sponge1
  sponge3 <- Sponge.absorb r sponge2
  { result: e } <- Sponge.squeeze sponge3
  -- 2. neg_pk = (pk.x, -pk.y), no constraint.
  let negPk = AffinePoint { x: pk.x, y: negate_ pk.y }
  -- 3. Unpack e to 255 LSB-first bits and scale.
  eBits <- unpack_ e (Proxy @255)
  ePkShifted <- scale pallasParams shifted shifted.zero negPk eBits
  -- 5. Chain via init: scale_known for s*G (fixed-base optimization,
  -- ~2× fewer kimchi gates than plain `scale` for 255-bit s).
  rShifted <- scaleKnown shifted (generator :: PallasG) sBits ePkShifted
  -- 6. Unshift_nonzero at the end.
  AffinePoint rPt <- shifted.unshiftNonzero rShifted
  -- 7. y_even: unpack_full + lt_bitstring_value canonical-form check,
  -- then take LSB. Mirrors production `is_even` (schnorr.ml:264-266 →
  -- Field.Checked.unpack_full → snark0.ml:470).
  yBits <- unpackFull rPt.y
  let yEven = not_ (Vector.head yBits)
  -- 8. r_correct. OCaml: `equal r rx` (r first, rx second);
  -- the arg order affects the generated coefficient signs in
  -- `addEqualsConstraint`'s two-variable case.
  rCorrect <- equals_ r rPt.x
  and_ rCorrect yEven
