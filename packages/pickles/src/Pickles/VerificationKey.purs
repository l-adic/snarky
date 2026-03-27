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

import Data.Array as Array
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable (foldl1)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, label, mul_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Prim.Int (class Add)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Plonk_verification_key_evals.Step.t
-- | Non-optional fields only (optional are all Opt.Nothing for Features.none).
type StepVK f =
  { sigmaComm :: Vector 7 (Array (AffinePoint f))
  , coefficientsComm :: Vector 15 (Array (AffinePoint f))
  , genericComm :: Array (AffinePoint f)
  , psmComm :: Array (AffinePoint f)
  , completeAddComm :: Array (AffinePoint f)
  , mulComm :: Array (AffinePoint f)
  , emulComm :: Array (AffinePoint f)
  , endomulScalarComm :: Array (AffinePoint f)
  }

-- | Step.map ~f — maps a function over each commitment array.
-- | OCaml record construction evaluates right-to-left.
mapStepVK :: forall a b. (a -> b) -> StepVK a -> StepVK b
mapStepVK f vk =
  -- Right-to-left: last field first
  let endomulScalarComm = map (mapPt f) vk.endomulScalarComm
      emulComm = map (mapPt f) vk.emulComm
      mulComm = map (mapPt f) vk.mulComm
      completeAddComm = map (mapPt f) vk.completeAddComm
      psmComm = map (mapPt f) vk.psmComm
      genericComm = map (mapPt f) vk.genericComm
      coefficientsComm = map (map (mapPt f)) vk.coefficientsComm
      sigmaComm = map (map (mapPt f)) vk.sigmaComm
  in { sigmaComm, coefficientsComm, genericComm, psmComm
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
  -- Vector.map2 (bs :> ...) keys ~f:(fun b key -> Step.map key ~f:(Array.map ~f:(fun g -> Double.map g ~f:((*) (b :> t)))))
  -- OCaml Vector.map2 evaluates right-to-left via :: constructor
  scaledRev <- traverse (\(Tuple b key) -> scaleVK b key) $
    Vector.reverse (Vector.zip bools keys)
  let scaled = Vector.reverse scaledRev
  -- Vector.reduce_exn ~f:(Step.map2 ~f:(Array.map2_exn ~f:(Double.map2 ~f:(+))))
  pure $ foldl1 addVK scaled
  where
  -- fun b key -> Step.map key ~f:(Array.map ~f:(fun g -> Double.map g ~f:((*) (b :> t))))
  scaleVK :: BoolVar f -> StepVK (FVar f) -> Snarky (KimchiConstraint f) t m (StepVK (FVar f))
  scaleVK b vk = do
    let bf = coerce b :: FVar f
    -- OCaml record fields evaluate right-to-left
    -- Each field: Array.map ~f:(fun g -> Double.map g ~f:((*) (b :> t)))
    -- OCaml Array.map evaluates right-to-left
    -- OCaml Double.map (x,y) ~f evaluates f y then f x
    endomulScalarComm <- scaleArr bf vk.endomulScalarComm
    emulComm <- scaleArr bf vk.emulComm
    mulComm <- scaleArr bf vk.mulComm
    completeAddComm <- scaleArr bf vk.completeAddComm
    psmComm <- scaleArr bf vk.psmComm
    genericComm <- scaleArr bf vk.genericComm
    -- Vector.map ~f also evaluates right-to-left
    coefficientsComm <- traverseRev (scaleArr bf) vk.coefficientsComm
    sigmaComm <- traverseRev (scaleArr bf) vk.sigmaComm
    pure { sigmaComm, coefficientsComm, genericComm, psmComm
         , completeAddComm, mulComm, emulComm, endomulScalarComm }

  scaleArr :: FVar f -> Array (AffinePoint (FVar f)) -> Snarky (KimchiConstraint f) t m (Array (AffinePoint (FVar f)))
  scaleArr bf arr = do
    -- Array.map right-to-left, Double.map (x,y) evaluates y first
    revResult <- traverse (\{ x, y } -> do
      y' <- mul_ bf y
      x' <- mul_ bf x
      pure { x: x', y: y' }) (Array.reverse arr)
    pure $ Array.reverse revResult

  traverseRev :: forall k a b_. Reflectable k Int => (a -> Snarky (KimchiConstraint f) t m b_) -> Vector k a -> Snarky (KimchiConstraint f) t m (Vector k b_)
  traverseRev f v = do
    rev <- traverse f (Vector.reverse v)
    pure $ Vector.reverse rev

  addVK :: StepVK (FVar f) -> StepVK (FVar f) -> StepVK (FVar f)
  addVK a b_ =
    { sigmaComm: Vector.zipWith (Array.zipWith addPt) a.sigmaComm b_.sigmaComm
    , coefficientsComm: Vector.zipWith (Array.zipWith addPt) a.coefficientsComm b_.coefficientsComm
    , genericComm: Array.zipWith addPt a.genericComm b_.genericComm
    , psmComm: Array.zipWith addPt a.psmComm b_.psmComm
    , completeAddComm: Array.zipWith addPt a.completeAddComm b_.completeAddComm
    , mulComm: Array.zipWith addPt a.mulComm b_.mulComm
    , emulComm: Array.zipWith addPt a.emulComm b_.emulComm
    , endomulScalarComm: Array.zipWith addPt a.endomulScalarComm b_.endomulScalarComm
    }

  addPt :: AffinePoint (FVar f) -> AffinePoint (FVar f) -> AffinePoint (FVar f)
  addPt p1 p2 = { x: add_ p1.x p2.x, y: add_ p1.y p2.y }
