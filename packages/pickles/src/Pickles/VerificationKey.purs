-- | Verification key shapes, and the projections that build them out
-- | of a kimchi `VerifierIndex`: `VerificationKey`, the positional
-- | newtype the circuit serialises; `StepVK`, the same commitments
-- | under names; and `chooseKey`, the in-circuit one-hot selection
-- | across a wrap circuit's branches.
module Pickles.VerificationKey
  ( VerificationKey(..)
  , extractWrapVKComms
  , extractWrapVKForStepHash
  , StepVK
  , chooseKey
  , VerifierIndexCommitments
  , pallasVerifierIndexCommitments
  , vestaVerifierIndexCommitments
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Newtype (over, over2)
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable (foldl1)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Field (StepField, WrapField)
import Pickles.Types (ChunkedCommitment(..))
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Proof (sigmaCommLast, verifierIndexColumnComms)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, Snarky, label, mul_, seal)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The plonk verification key: 7 sigma, 15 coefficient and 6 index
-- | commitments, each carrying `stepChunks` curve points, one per slice
-- | kimchi splits the polynomial into.
-- |
-- | A newtype and not a bare record, because the `CircuitType` instance
-- | below serialises sigma, then coefficients, then index — not the
-- | alphabetical order a record would pick up. The six index
-- | commitments are generic, psm, completeAdd, mul, emul,
-- | endomulScalar, in that order.
-- |
-- | `pt` lets the one type serve value and var forms on either Pasta
-- | curve.
newtype VerificationKey :: Int -> Type -> Type
newtype VerificationKey stepChunks pt = VerificationKey
  { sigma :: Vector 7 (ChunkedCommitment stepChunks pt)
  , coeff :: Vector 15 (ChunkedCommitment stepChunks pt)
  , index :: Vector 6 (ChunkedCommitment stepChunks pt)
  }

instance
  ( CircuitType f a var
  , Reflectable stepChunks Int
  ) =>
  CircuitType f (VerificationKey stepChunks a) (VerificationKey stepChunks var) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple3 (Vector 7 (ChunkedCommitment stepChunks a)) (Vector 15 (ChunkedCommitment stepChunks a)) (Vector 6 (ChunkedCommitment stepChunks a))))
  valueToFields (VerificationKey r) = genericValueToFields (tuple3 r.sigma r.coeff r.index)
  fieldsToValue fs =
    let
      tup :: Tuple3 (Vector 7 (ChunkedCommitment stepChunks a)) (Vector 15 (ChunkedCommitment stepChunks a)) (Vector 6 (ChunkedCommitment stepChunks a))
      tup = genericFieldsToValue fs
    in
      uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup
  varToFields (VerificationKey r) = genericVarToFields
    @(Tuple3 (Vector 7 (ChunkedCommitment stepChunks a)) (Vector 15 (ChunkedCommitment stepChunks a)) (Vector 6 (ChunkedCommitment stepChunks a)))
    (tuple3 r.sigma r.coeff r.index)
  fieldsToVar fs =
    let
      tup :: Tuple3 (Vector 7 (ChunkedCommitment stepChunks var)) (Vector 15 (ChunkedCommitment stepChunks var)) (Vector 6 (ChunkedCommitment stepChunks var))
      tup = genericFieldsToVar
        @(Tuple3 (Vector 7 (ChunkedCommitment stepChunks a)) (Vector 15 (ChunkedCommitment stepChunks a)) (Vector 6 (ChunkedCommitment stepChunks a)))
        fs
    in
      uncurry3 (\sigma coeff index -> VerificationKey { sigma, coeff, index }) tup

instance (CheckedType f c var) => CheckedType f c (VerificationKey stepChunks var) where
  check (VerificationKey r) = check (tuple3 r.sigma r.coeff r.index)

-- | A wrap `VerifierIndex`'s commitments in `VerificationKey` shape.
-- | Its points are Pallas, whose coordinates already lie in
-- | `StepField`, so nothing crosses fields.
-- |
-- | `wrapVkChunks` is this VK's own chunk count — a property of the
-- | compile that produced it, not of the circuit consuming it, and
-- | distinct from the wrap circuit's `stepChunks` and from a
-- | side-loaded slot's `slotVkChunks`.
extractWrapVKComms
  :: forall @wrapVkChunks
   . Reflectable wrapVkChunks Int
  => VerifierIndex Pallas.G Pallas.ScalarField
  -> VerificationKey wrapVkChunks (WeierstrassAffinePoint Pallas.G (F Vesta.ScalarField))
extractWrapVKComms vk =
  let
    comms = vestaVerifierIndexCommitments @wrapVkChunks vk

    wrapPt :: AffinePoint Vesta.ScalarField -> WeierstrassAffinePoint Pallas.G (F Vesta.ScalarField)
    wrapPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map (over ChunkedCommitment (map wrapPt)) comms.sigma
      , coeff: map (over ChunkedCommitment (map wrapPt)) comms.coeff
      , index: map (over ChunkedCommitment (map wrapPt)) comms.index
      }

-- | Verifier-index polynomial commitments, in the three groups
-- | consumers work with:
-- |   `index`  = 6 selector commitments (generic, psm, completeAdd,
-- |              mul, emul, endomulScalar)
-- |   `coeff`  = 15 coefficient commitments
-- |   `sigma`  = 7 sigma commitments, the first 6 from
-- |              `verifierIndexColumnComms` and the last from
-- |              `sigmaCommLast`
-- |
-- | Each commitment carries `stepChunks` curve points; the outer sizes
-- | and the chunk count are both static.
type VerifierIndexCommitments :: Int -> Type -> Type
type VerifierIndexCommitments stepChunks f =
  { index :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint f))
  , coeff :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , sigma :: Vector 7 (ChunkedCommitment stepChunks (AffinePoint f))
  }

-- | `splitVkCommitments` over a step verifier index, whose VK the wrap
-- | circuit consumes. Pass `@stepChunks` matching the chunk count on
-- | the index's commitments.
pallasVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Vesta.G Pallas.BaseField
  -> VerifierIndexCommitments stepChunks Pallas.ScalarField
pallasVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (verifierIndexColumnComms vk) (sigmaCommLast vk)

-- | `splitVkCommitments` over a wrap verifier index, whose VK the step
-- | circuit consumes.
vestaVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Pallas.G Vesta.BaseField
  -> VerifierIndexCommitments stepChunks Vesta.ScalarField
vestaVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (verifierIndexColumnComms vk) (sigmaCommLast vk)

-- | Splits the raw column commitments, whose layout is fixed at
-- | `[ index(6) ; coeff(15) ; sigma-except-last(6) ]` = 27 entries,
-- | each an `Array (AffinePoint f)` of `stepChunks` chunks. `sigmaLast`
-- | is snoc'd on to give the 7 sigma commitments. A chunk count that
-- | disagrees with `@stepChunks` panics through `fromJust'`.
splitVkCommitments
  :: forall @stepChunks f
   . Reflectable stepChunks Int
  => Array (Array (AffinePoint f))
  -> Array (AffinePoint f)
  -> VerifierIndexCommitments stepChunks f
splitVkCommitments raw sigmaLast =
  let
    toChunks :: Array (AffinePoint f) -> ChunkedCommitment stepChunks (AffinePoint f)
    toChunks = ChunkedCommitment <<< fromJust' "VerifierIndex commitment chunks length mismatch with @stepChunks"
      <<< Vector.toVector @stepChunks
    mkIndex = fromJust' "VerifierIndex index commits (6 entries)"
      <<< Vector.toVector @6
    mkCoeff = fromJust' "VerifierIndex coeff commits (15 entries)"
      <<< Vector.toVector @15
    mkSigma6 = fromJust' "VerifierIndex sigma commits (6 entries, pre-sigmaLast)"
      <<< Vector.toVector @6
    rawChunked = map toChunks raw
    sigmaLastChunked = toChunks sigmaLast
  in
    { index: mkIndex (Array.take 6 rawChunked)
    , coeff: mkCoeff (Array.take 15 (Array.drop 6 rawChunked))
    , sigma: Vector.snoc (mkSigma6 (Array.drop 21 rawChunked)) sigmaLastChunked
    }

-- | The same commitments as `VerificationKey`, under names and with
-- | the six index commitments split out. The feature-gated commitments
-- | are absent; they are all empty for the feature set these circuits
-- | use.
type StepVK :: Int -> Type -> Type
type StepVK stepChunks f =
  { sigmaComm :: Vector 7 (ChunkedCommitment stepChunks (AffinePoint f))
  , coefficientsComm :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , genericComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , psmComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , completeAddComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , mulComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , emulComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , endomulScalarComm :: ChunkedCommitment stepChunks (AffinePoint f)
  }

-- | A compiled wrap verifier index as a `StepVK`: the commitments that
-- | go into the messages-for-next-step-proof digest. Built by
-- | `Pickles.Prove.Step` and, from the real wrap VK, by the
-- | out-of-circuit `Pickles.Verify`, which recomputes that digest.
extractWrapVKForStepHash
  :: forall @wrapVkChunks
   . Reflectable wrapVkChunks Int
  => VerifierIndex Pallas.G WrapField
  -> StepVK wrapVkChunks StepField
extractWrapVKForStepHash vk =
  let
    comms = vestaVerifierIndexCommitments @wrapVkChunks vk
  in
    { sigmaComm: comms.sigma
    , coefficientsComm: comms.coeff
    , genericComm: Vector.index comms.index (unsafeFinite @6 0)
    , psmComm: Vector.index comms.index (unsafeFinite @6 1)
    , completeAddComm: Vector.index comms.index (unsafeFinite @6 2)
    , mulComm: Vector.index comms.index (unsafeFinite @6 3)
    , emulComm: Vector.index comms.index (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index comms.index (unsafeFinite @6 5)
    }

-- | The step VK a one-hot branch vector selects: every commitment
-- | scaled by its branch boolean, summed pointwise across branches,
-- | then sealed. Scale, add and seal all map over the chunk dimension.
chooseKey
  :: forall stepChunks n nPred f r
   . PrimeField f
  => Reflectable n Int
  => Reflectable stepChunks Int
  => Add 1 nPred n
  => Vector n (BoolVar f)
  -> Vector n (StepVK stepChunks (FVar f))
  -> Snarky f (KimchiConstraint f) r (StepVK stepChunks (FVar f))
chooseKey bools keys = label "choose-key" do
  -- Traversal order here is load-bearing: branches, record fields,
  -- vector fields and the two coordinates are all visited in reverse,
  -- chunks forwards. These gates are diffed against the OCaml wrap
  -- verifier's by `pickles-circuit-diffs`, so reordering any of them
  -- changes the circuit.
  scaledRev <- traverse (\(Tuple b key) -> scaleVK b key) $
    Vector.reverse (Vector.zip bools keys)
  let scaled = Vector.reverse scaledRev
  let reduced = foldl1 addVK scaled
  sealVK reduced
  where
  -- `y` scaled before `x`.
  scalePt :: FVar f -> AffinePoint (FVar f) -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
  scalePt bf (AffinePoint { x, y }) = do
    y' <- mul_ bf y
    x' <- mul_ bf x
    pure (AffinePoint { x: x', y: y' })

  -- Chunks are the one dimension scaled first to last, so a plain
  -- `traverse` is right here and `traverseRev` is wrong.
  scalePtChunks
    :: FVar f
    -> ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> Snarky f (KimchiConstraint f) r (ChunkedCommitment stepChunks (AffinePoint (FVar f)))
  scalePtChunks bf cc = ChunkedCommitment <$> traverse (scalePt bf) (coerce cc)

  scaleVK :: BoolVar f -> StepVK stepChunks (FVar f) -> Snarky f (KimchiConstraint f) r (StepVK stepChunks (FVar f))
  scaleVK b vk = do
    let bf = coerce b :: FVar f
    -- Record fields in reverse declaration order.
    endomulScalarComm <- scalePtChunks bf vk.endomulScalarComm
    emulComm <- scalePtChunks bf vk.emulComm
    mulComm <- scalePtChunks bf vk.mulComm
    completeAddComm <- scalePtChunks bf vk.completeAddComm
    psmComm <- scalePtChunks bf vk.psmComm
    genericComm <- scalePtChunks bf vk.genericComm
    -- Vector fields likewise.
    coefficientsComm <- traverseRev (scalePtChunks bf) vk.coefficientsComm
    sigmaComm <- traverseRev (scalePtChunks bf) vk.sigmaComm
    pure
      { sigmaComm
      , coefficientsComm
      , genericComm
      , psmComm
      , completeAddComm
      , mulComm
      , emulComm
      , endomulScalarComm
      }

  traverseRev :: forall k a b_. Reflectable k Int => (a -> Snarky f (KimchiConstraint f) r b_) -> Vector k a -> Snarky f (KimchiConstraint f) r (Vector k b_)
  traverseRev f v = do
    rev <- traverse f (Vector.reverse v)
    pure $ Vector.reverse rev

  -- `y` sealed before `x`, as in `scalePt`.
  sealPt :: AffinePoint (FVar f) -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
  sealPt (AffinePoint { x, y }) = do
    y' <- seal y
    x' <- seal x
    pure (AffinePoint { x: x', y: y' })

  sealPtChunks
    :: ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> Snarky f (KimchiConstraint f) r (ChunkedCommitment stepChunks (AffinePoint (FVar f)))
  sealPtChunks cc = ChunkedCommitment <$> traverse sealPt (coerce cc)

  sealVK :: StepVK stepChunks (FVar f) -> Snarky f (KimchiConstraint f) r (StepVK stepChunks (FVar f))
  sealVK vk = do
    endomulScalarComm <- sealPtChunks vk.endomulScalarComm
    emulComm <- sealPtChunks vk.emulComm
    mulComm <- sealPtChunks vk.mulComm
    completeAddComm <- sealPtChunks vk.completeAddComm
    psmComm <- sealPtChunks vk.psmComm
    genericComm <- sealPtChunks vk.genericComm
    coefficientsComm <- traverseRev sealPtChunks vk.coefficientsComm
    sigmaComm <- traverseRev sealPtChunks vk.sigmaComm
    pure
      { sigmaComm
      , coefficientsComm
      , genericComm
      , psmComm
      , completeAddComm
      , mulComm
      , emulComm
      , endomulScalarComm
      }

  addVK :: StepVK stepChunks (FVar f) -> StepVK stepChunks (FVar f) -> StepVK stepChunks (FVar f)
  addVK a b_ =
    { sigmaComm: Vector.zipWith addPtChunks a.sigmaComm b_.sigmaComm
    , coefficientsComm: Vector.zipWith addPtChunks a.coefficientsComm b_.coefficientsComm
    , genericComm: addPtChunks a.genericComm b_.genericComm
    , psmComm: addPtChunks a.psmComm b_.psmComm
    , completeAddComm: addPtChunks a.completeAddComm b_.completeAddComm
    , mulComm: addPtChunks a.mulComm b_.mulComm
    , emulComm: addPtChunks a.emulComm b_.emulComm
    , endomulScalarComm: addPtChunks a.endomulScalarComm b_.endomulScalarComm
    }

  addPtChunks
    :: ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> ChunkedCommitment stepChunks (AffinePoint (FVar f))
  addPtChunks = over2 ChunkedCommitment (Vector.zipWith addPt)

  addPt :: AffinePoint (FVar f) -> AffinePoint (FVar f) -> AffinePoint (FVar f)
  addPt (AffinePoint p1) (AffinePoint p2) = AffinePoint { x: add_ p1.x p2.x, y: add_ p1.y p2.y }
