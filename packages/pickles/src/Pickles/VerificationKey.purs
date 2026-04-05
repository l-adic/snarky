-- | Step verification key and choose_key.
-- |
-- | Reference: mina/src/lib/crypto/kimchi_backend/common/plonk_verification_key_evals.ml
-- |            mina/src/lib/crypto/pickles/wrap_verifier.ml:212-310
module Pickles.VerificationKey
  ( StepVK
  , mapStepVK
  , chooseKey
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable (foldl1)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, label, mul_, seal)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Plonk_verification_key_evals.t
-- | Non-optional fields only (optional are all Opt.Nothing for Features.none).
-- | Each field is a single commitment (curve point), not an array.
-- | OCaml: 'comm t where 'comm is instantiated to a curve point.
type StepVK f =
  { sigmaComm :: Vector 7 (AffinePoint f)
  , coefficientsComm :: Vector 15 (AffinePoint f)
  , genericComm :: AffinePoint f
  , psmComm :: AffinePoint f
  , completeAddComm :: AffinePoint f
  , mulComm :: AffinePoint f
  , emulComm :: AffinePoint f
  , endomulScalarComm :: AffinePoint f
  }

-- | Step.map ~f — maps a function over each commitment.
-- | OCaml record construction evaluates right-to-left.
mapStepVK :: forall a b. (a -> b) -> StepVK a -> StepVK b
mapStepVK f vk =
  -- Right-to-left: last field first
  let
    endomulScalarComm = mapPt f vk.endomulScalarComm
    emulComm = mapPt f vk.emulComm
    mulComm = mapPt f vk.mulComm
    completeAddComm = mapPt f vk.completeAddComm
    psmComm = mapPt f vk.psmComm
    genericComm = mapPt f vk.genericComm
    coefficientsComm = map (mapPt f) vk.coefficientsComm
    sigmaComm = map (mapPt f) vk.sigmaComm
  in
    { sigmaComm, coefficientsComm, genericComm, psmComm
    , completeAddComm, mulComm, emulComm, endomulScalarComm }
  where
  mapPt g { x, y } = { x: g x, y: g y }

-- | Wrap_verifier.choose_key
-- |
-- | For each branch, scales all VK commitments by the branch boolean.
-- | Then reduces across branches by pointwise addition.
-- | Optional commitments resolve to Opt.Nothing for Features.none (0 constraints).
-- |
-- | Reference: wrap_verifier.ml:212-310
chooseKey
  :: forall n _m f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Add 1 _m n
  => Vector n (BoolVar f)
  -> Vector n (StepVK (FVar f))
  -> Snarky (KimchiConstraint f) t m (StepVK (FVar f))
chooseKey bools keys = label "choose-key" do
  -- OCaml Vector.map2 evaluates right-to-left via :: constructor
  scaledRev <- traverse (\(Tuple b key) -> scaleVK b key) $
    Vector.reverse (Vector.zip bools keys)
  let scaled = Vector.reverse scaledRev
  let reduced = foldl1 addVK scaled
  -- wrap_verifier.ml:321-322: Step.map ~f:(Double.map ~f:seal)
  sealVK reduced
  where
  -- Scale each commitment point by the branch boolean.
  -- OCaml: Double.map g ~f:((*) (b :> t)) — evaluates y first (right-to-left)
  scalePt :: FVar f -> AffinePoint (FVar f) -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  scalePt bf { x, y } = do
    y' <- mul_ bf y
    x' <- mul_ bf x
    pure { x: x', y: y' }

  scaleVK :: BoolVar f -> StepVK (FVar f) -> Snarky (KimchiConstraint f) t m (StepVK (FVar f))
  scaleVK b vk = do
    let bf = coerce b :: FVar f
    -- OCaml record fields evaluate right-to-left
    endomulScalarComm <- scalePt bf vk.endomulScalarComm
    emulComm <- scalePt bf vk.emulComm
    mulComm <- scalePt bf vk.mulComm
    completeAddComm <- scalePt bf vk.completeAddComm
    psmComm <- scalePt bf vk.psmComm
    genericComm <- scalePt bf vk.genericComm
    -- Vector.map ~f also evaluates right-to-left
    coefficientsComm <- traverseRev (scalePt bf) vk.coefficientsComm
    sigmaComm <- traverseRev (scalePt bf) vk.sigmaComm
    pure { sigmaComm, coefficientsComm, genericComm, psmComm
         , completeAddComm, mulComm, emulComm, endomulScalarComm }

  traverseRev :: forall k a b_. Reflectable k Int => (a -> Snarky (KimchiConstraint f) t m b_) -> Vector k a -> Snarky (KimchiConstraint f) t m (Vector k b_)
  traverseRev f v = do
    rev <- traverse f (Vector.reverse v)
    pure $ Vector.reverse rev

  -- Seal all coordinates (wrap_verifier.ml:321-322)
  -- OCaml: Double.map ~f:seal — evaluates y first
  sealPt :: AffinePoint (FVar f) -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  sealPt { x, y } = do
    y' <- seal y
    x' <- seal x
    pure { x: x', y: y' }

  sealVK :: StepVK (FVar f) -> Snarky (KimchiConstraint f) t m (StepVK (FVar f))
  sealVK vk = do
    endomulScalarComm <- sealPt vk.endomulScalarComm
    emulComm <- sealPt vk.emulComm
    mulComm <- sealPt vk.mulComm
    completeAddComm <- sealPt vk.completeAddComm
    psmComm <- sealPt vk.psmComm
    genericComm <- sealPt vk.genericComm
    coefficientsComm <- traverseRev sealPt vk.coefficientsComm
    sigmaComm <- traverseRev sealPt vk.sigmaComm
    pure { sigmaComm, coefficientsComm, genericComm, psmComm
         , completeAddComm, mulComm, emulComm, endomulScalarComm }

  addVK :: StepVK (FVar f) -> StepVK (FVar f) -> StepVK (FVar f)
  addVK a b_ =
    { sigmaComm: Vector.zipWith addPt a.sigmaComm b_.sigmaComm
    , coefficientsComm: Vector.zipWith addPt a.coefficientsComm b_.coefficientsComm
    , genericComm: addPt a.genericComm b_.genericComm
    , psmComm: addPt a.psmComm b_.psmComm
    , completeAddComm: addPt a.completeAddComm b_.completeAddComm
    , mulComm: addPt a.mulComm b_.mulComm
    , emulComm: addPt a.emulComm b_.emulComm
    , endomulScalarComm: addPt a.endomulScalarComm b_.endomulScalarComm
    }

  addPt :: AffinePoint (FVar f) -> AffinePoint (FVar f) -> AffinePoint (FVar f)
  addPt p1 p2 = { x: add_ p1.x p2.x, y: add_ p1.y p2.y }
