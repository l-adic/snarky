-- | Wrap verification key shape (Plonk_verification_key_evals) plus
-- | Step VK helpers (`StepVK` named-field shape, `chooseKey`).
-- |
-- | Reference: mina/src/lib/crypto/kimchi_backend/common/plonk_verification_key_evals.ml
-- |            mina/src/lib/crypto/pickles/wrap_verifier.ml:212-310
module Pickles.VerificationKey
  ( VerificationKey(..)
  , extractWrapVKComms
  , StepVK
  , chooseKey
  , VerifierIndexCommitments
  , pallasVerifierIndexCommitments
  , vestaVerifierIndexCommitments
  ) where

import Prelude

import Data.Array as Array
import Data.Newtype (over, over2)
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable (foldl1)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Backend.Kimchi.Proof (sigmaCommLast, verifierIndexColumnComms)
import Pickles.Types (ChunkedCommitment(..))
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, label, mul_, seal)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Plonk verification key: sigma(7), coefficients(15), index(6)
-- | commitments. Each commitment carries `stepChunks` curve points
-- | (kimchi splits each polynomial commitment into `stepChunks` slices
-- | of `max_poly_size`; OCaml mirrors this with `'comm = Inner_curve.t
-- | array`).
-- |
-- | OCaml hlist order: sigma_comm, coefficients_comm, index commitments
-- | (generic, psm, complete_add, mul, emul, endomul_scalar).
-- |
-- | The element type `pt` lets the same newtype serve both value and var
-- | representations on either Pasta curve; `stepChunks` matches kimchi's
-- | `comm.chunks.len()`. The wrap-VK consumer side currently fixes
-- | `stepChunks = 1` per OCaml `step_main.ml:347`
-- | (`num_chunks_by_default`), but we keep it polymorphic so the type
-- | tracks the future-extensibility flagged by the OCaml TODO.
-- |
-- | Reference: plonk_verification_key_evals.ml
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

-- | Project σ / coeff / index commitments out of a hydrated kimchi
-- | wrap `VerifierIndex` into the in-circuit-shaped `VerificationKey`.
-- | The wrap VK's commitments are Pallas points with coordinates in
-- | Pallas.BaseField = Vesta.ScalarField (= the step circuit's field),
-- | so no cross-field coercion is needed.
-- |
-- | Polymorphic on `wrapVkChunks` — the chunk count carried by THIS
-- | wrap VK (a property of the producing compile, not the consuming
-- | circuit). Distinct from the wrap circuit's own `stepChunks`
-- | (Dim 1, = the step proof's chunks) and from a side-loaded slot's
-- | chunks (Dim 3, = the slot's `nc`). Callers pass `@wrapVkChunks`
-- | from whichever compile produced this VK. OCaml fixes the wrap-VK
-- | consumer to `num_chunks_by_default = 1` (see `step_main.ml:347`).
extractWrapVKComms
  :: forall @wrapVkChunks
   . Reflectable wrapVkChunks Int
  => VerifierIndex Pallas.G Pallas.ScalarField
  -> VerificationKey wrapVkChunks (WeierstrassAffinePoint Pallas.G (F Vesta.ScalarField))
extractWrapVKComms vk =
  let
    comms = vestaVerifierIndexCommitments @wrapVkChunks vk

    wrapPt :: AffinePoint Vesta.ScalarField -> WeierstrassAffinePoint Pallas.G (F Vesta.ScalarField)
    wrapPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map (over ChunkedCommitment (map wrapPt)) comms.sigma
      , coeff: map (over ChunkedCommitment (map wrapPt)) comms.coeff
      , index: map (over ChunkedCommitment (map wrapPt)) comms.index
      }

-- | Verifier-index polynomial commitments, split into the three groups
-- | Pickles consumers actually work with. Layout (matches OCaml
-- | `Plonk_verification_key_evals`):
-- |   `index`  = 6 selector commitments (generic, psm, complete_add, mul,
-- |              emul, endomul_scalar)
-- |   `coeff`  = 15 coefficient commitments
-- |   `sigma`  = 7 sigma commitments (6 from `*VerifierIndexColumnComms`
-- |              + 1 from `*SigmaCommLast`, snoc'd into a Vector 7)
-- |
-- | Each commitment carries `stepChunks` curve points; both the outer
-- | Vector sizes AND the inner chunk count are static.
-- |
-- | Wrap-side consumers (where OCaml currently hardcodes
-- | `num_chunks_by_default = 1` per `step_main.ml:347`) call with
-- | `@1`; step-side consumers (`wrap_main.ml:80`'s `~num_chunks`)
-- | pass the user-supplied compile param. The specialization is
-- | pushed all the way to the consumer so the projection stays a
-- | one-liner over the raw `Snarky.Backend.Kimchi.Proof` bindings.
type VerifierIndexCommitments :: Int -> Type -> Type
type VerifierIndexCommitments stepChunks f =
  { index :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint f))
  , coeff :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , sigma :: Vector 7 (ChunkedCommitment stepChunks (AffinePoint f))
  }

-- | Vector-typed split of `verifierIndexColumnComms` +
-- | `sigmaCommLast`. Used for step VK extraction (consumed by
-- | the wrap circuit). Pass `@stepChunks` matching kimchi's
-- | `comm.chunks.len()`.
pallasVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Vesta.G Pallas.BaseField
  -> VerifierIndexCommitments stepChunks Pallas.ScalarField
pallasVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (verifierIndexColumnComms vk) (sigmaCommLast vk)

-- | Vector-typed split of `verifierIndexColumnComms` +
-- | `sigmaCommLast`. Used for wrap VK extraction (consumed by
-- | the step circuit). OCaml fixes this to `@1` at
-- | `step_main.ml:347` (TODO in OCaml flags future extensibility);
-- | callers here also pass `@1` until that invariant changes.
vestaVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Pallas.G Vesta.BaseField
  -> VerifierIndexCommitments stepChunks Vesta.ScalarField
vestaVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (verifierIndexColumnComms vk) (sigmaCommLast vk)

-- | Shared splitter. Raw layout:
-- |   [ index(6) ; coeff(15) ; sigma-except-last(6) ]  = 27 commitments,
-- |   each entry an `Array (AffinePoint f)` of length stepChunks.
-- | `sigmaLast` (also chunked) is snoc'd onto `sigma6` to produce
-- | the exported `Vector 7`. Inner Arrays reshape to
-- | `Vector stepChunks` — a length mismatch panics via `fromJust'`.
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

-- | Plonk_verification_key_evals.Step.t
-- | Non-optional fields only (optional are all Opt.Nothing for Features.none).
-- |
-- | At num_chunks > 1 (circuit domain > SRS max_poly_size), each polynomial
-- | commitment splits into `stepChunks` curve points (each chunk commits to
-- | one slice of the polynomial). OCaml mirrors this with
-- | `'comm = Inner_curve.t array`. We parameterize `StepVK` by `stepChunks`
-- | so chooseKey / chunked-MSM operations propagate per chunk.
-- |
-- | Reference: OCaml `Plonk_verification_key_evals.Step` and
-- | `wrap_verifier.ml:290-313`'s `Array.map g ~f:(Double.map …)` per chunk.
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

-- | Wrap_verifier.choose_key
-- |
-- | For each branch, scales all VK commitments by the branch boolean.
-- | Then reduces across branches by pointwise addition.
-- | Optional commitments resolve to Opt.Nothing for Features.none (0 constraints).
-- |
-- | At `stepChunks > 1` each commitment is `Vector stepChunks (AffinePoint f)`
-- | and the scale / add / seal operations map over the chunk dimension
-- | (mirroring OCaml `wrap_verifier.ml:296-310`'s
-- | `Array.map g ~f:(Double.map ~f:((*) b))`).
-- |
-- | Reference: wrap_verifier.ml:212-310
chooseKey
  :: forall stepChunks n nPred f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Reflectable stepChunks Int
  => Add 1 nPred n
  => Vector n (BoolVar f)
  -> Vector n (StepVK stepChunks (FVar f))
  -> Snarky (KimchiConstraint f) t m (StepVK stepChunks (FVar f))
chooseKey bools keys = label "choose-key" do
  -- OCaml Vector.map2 evaluates right-to-left via :: constructor
  scaledRev <- traverse (\(Tuple b key) -> scaleVK b key) $
    Vector.reverse (Vector.zip bools keys)
  let scaled = Vector.reverse scaledRev
  let reduced = foldl1 addVK scaled
  -- wrap_verifier.ml:321-322: Step.map ~f:(Double.map ~f:seal)
  sealVK reduced
  where
  -- Scale a single curve point by the branch boolean. OCaml
  -- `Double.map g ~f:((*) (b :> t))` evaluates y first (right-to-left).
  scalePt :: FVar f -> AffinePoint (FVar f) -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  scalePt bf { x, y } = do
    y' <- mul_ bf y
    x' <- mul_ bf x
    pure { x: x', y: y' }

  -- Scale every chunk of a chunked commitment. OCaml
  -- `Array.map g ~f:(Double.map ~f:((*) b))` maps over the chunk array.
  -- PureScript `traverse` is left-to-right; the OCaml `Array.map`
  -- direction is unspecified for arrays of length-1, but for nc > 1
  -- this must mirror OCaml's iteration order. OCaml's `Array.map` is
  -- LEFT-TO-RIGHT (unlike List/Vector.map which are right-to-left via
  -- `::`), so straight `traverse` is correct.
  scalePtChunks
    :: FVar f
    -> ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> Snarky (KimchiConstraint f) t m (ChunkedCommitment stepChunks (AffinePoint (FVar f)))
  scalePtChunks bf cc = ChunkedCommitment <$> traverse (scalePt bf) (coerce cc)

  scaleVK :: BoolVar f -> StepVK stepChunks (FVar f) -> Snarky (KimchiConstraint f) t m (StepVK stepChunks (FVar f))
  scaleVK b vk = do
    let bf = coerce b :: FVar f
    -- OCaml record fields evaluate right-to-left
    endomulScalarComm <- scalePtChunks bf vk.endomulScalarComm
    emulComm <- scalePtChunks bf vk.emulComm
    mulComm <- scalePtChunks bf vk.mulComm
    completeAddComm <- scalePtChunks bf vk.completeAddComm
    psmComm <- scalePtChunks bf vk.psmComm
    genericComm <- scalePtChunks bf vk.genericComm
    -- Vector.map ~f also evaluates right-to-left
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

  sealPtChunks
    :: ChunkedCommitment stepChunks (AffinePoint (FVar f))
    -> Snarky (KimchiConstraint f) t m (ChunkedCommitment stepChunks (AffinePoint (FVar f)))
  sealPtChunks cc = ChunkedCommitment <$> traverse sealPt (coerce cc)

  sealVK :: StepVK stepChunks (FVar f) -> Snarky (KimchiConstraint f) t m (StepVK stepChunks (FVar f))
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
  addPt p1 p2 = { x: add_ p1.x p2.x, y: add_ p1.y p2.y }
