module Pickles.CircuitDiffs.PureScript.CheckBulletproofWrap
  ( compileCheckBulletproofWrap
  ) where

import Prelude

import Data.Fin (reflectFinite)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple10, Tuple2, tuple10, tuple2, uncurry10, uncurry2)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, wrapEndo)
import Pickles.Field (WrapField)
import Pickles.IPA (checkBulletproof)
import Pickles.Sponge (evalSpongeM)
import Pickles.Wrap.OtherField as WrapOtherField
import RandomOracle.Sponge (SpongeState(..))
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `check_bulletproof_wrap_circuit`'s input (OCaml `dump_circuit_impl.ml`): the sponge state
-- | at `sponge_before_evaluations` (mode `Squeezed 1`), `xi`, the two `sg_old` mask bits, the
-- | 47 MSM bases (two `sg_old`, `x_hat`, `ft_comm`, `z_comm`, the six index commitments, the 15
-- | `w_comm`, the 15 coefficient commitments, the six `sigma_comm`), the opening, then the
-- | Type1-shifted deferred `cip` and `b`.
newtype CheckBulletproofWrapInput b f pt s = CheckBulletproofWrapInput
  { sponge :: Vector 3 f
  , xi :: SizedF 128 f
  , sgOldMask :: Vector 2 b
  , bases :: Vector 47 pt
  , lr :: Vector 16 { l :: pt, r :: pt }
  , delta :: pt
  , sg :: pt
  , z1 :: s
  , z2 :: s
  , combinedInnerProduct :: s
  , b :: s
  }

-- | The wire order; the deferred pair travels as one tuple, past `Data.Tuple.Nested`'s ten.
type CheckBulletproofWrapTuple b f pt s =
  Tuple10 (Vector 3 f) (SizedF 128 f) (Vector 2 b) (Vector 47 pt) (Vector 16 { l :: pt, r :: pt }) pt pt s s
    (Tuple2 s s)

toTuple :: forall b f pt s. CheckBulletproofWrapInput b f pt s -> CheckBulletproofWrapTuple b f pt s
toTuple (CheckBulletproofWrapInput i) =
  tuple10 i.sponge i.xi i.sgOldMask i.bases i.lr i.delta i.sg i.z1 i.z2
    (tuple2 i.combinedInnerProduct i.b)

fromTuple :: forall b f pt s. CheckBulletproofWrapTuple b f pt s -> CheckBulletproofWrapInput b f pt s
fromTuple = uncurry10 \sponge xi sgOldMask bases lr delta sg z1 z2 deferred ->
  deferred # uncurry2 \combinedInnerProduct b ->
    CheckBulletproofWrapInput
      { sponge, xi, sgOldMask, bases, lr, delta, sg, z1, z2, combinedInnerProduct, b }

instance
  ( CircuitType f ba bv
  , CircuitType f fa fv
  , CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (CheckBulletproofWrapInput ba fa pa sa) (CheckBulletproofWrapInput bv fv pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CheckBulletproofWrapTuple ba fa pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CheckBulletproofWrapTuple ba fa pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(CheckBulletproofWrapTuple ba fa pa sa)

-- | The library gadget `Pickles.IPA.checkBulletproof` on the wrap side, the two `sg_old`
-- | bases under their mask bits, from the given squeezed sponge; the success bit and the
-- | challenges are left unasserted, as the gadget returns them.
checkBulletproofWrapCircuit
  :: forall r
   . AffinePoint (F WrapField)
  -> UnChecked
       ( CheckBulletproofWrapInput (BoolVar WrapField) (FVar WrapField) (AffinePoint (FVar WrapField))
           (Type1 (FVar WrapField))
       )
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
checkBulletproofWrapCircuit blindingH (UnChecked (CheckBulletproofWrapInput i)) = do
  let
    AffinePoint { x: F hx, y: F hy } = blindingH
    params = { endo: const_ wrapEndo, groupMapParams: groupMapParams (Proxy @VestaG) }
    sponge = { state: i.sponge, spongeState: Squeezed (reflectFinite @1) }
    masks = map Just i.sgOldMask `Vector.append` Vector.replicate Nothing
  _ <- evalSpongeM sponge $
    checkBulletproof @WrapField @VestaG WrapOtherField.ipaScalarOps params i.bases masks
      { xi: i.xi
      , deferred: { combinedInnerProduct: i.combinedInnerProduct, b: i.b }
      , opening: { lr: i.lr, z1: i.z1, z2: i.z2, delta: i.delta, sg: i.sg }
      , blindingGenerator: AffinePoint { x: const_ hx, y: const_ hy }
      }
  pure unit

compileCheckBulletproofWrap :: AffinePoint (F WrapField) -> Effect (CompiledCircuit WrapField)
compileCheckBulletproofWrap blindingH =
  compile noAdvice
    ( Proxy
        @( UnChecked
            (CheckBulletproofWrapInput Boolean (F WrapField) (AffinePoint WrapField) (Type1 (F WrapField)))
        )
    )
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (checkBulletproofWrapCircuit blindingH)
