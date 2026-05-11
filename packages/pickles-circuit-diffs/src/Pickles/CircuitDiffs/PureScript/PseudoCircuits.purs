module Pickles.CircuitDiffs.PureScript.PseudoCircuits
  ( compileChooseKeyN1Wrap
  , compileOneHotN1Step
  , compileOneHotN1Wrap
  , compileOneHotN3Step
  , compileOneHotN3Wrap
  , compilePseudoMaskN1Step
  , compilePseudoMaskN1Wrap
  , compilePseudoMaskN3Step
  , compilePseudoMaskN3Wrap
  , compilePseudoChooseN1Step
  , compilePseudoChooseN1Wrap
  , compilePseudoChooseN3Step
  , compilePseudoChooseN3Wrap
  , compileUtilsOnesVectorN16Step
  , compileUtilsOnesVectorN16Wrap
  , compileOneHotN17Step
  , compileOneHotN17Wrap
  , compilePseudoMaskN17Step
  , compilePseudoMaskN17Wrap
  , compileSideloadedVkTypStep
  ) where

-- | Pseudo module sub-circuit tests matching OCaml fixtures.
-- | Each circuit takes a flat input array and calls the corresponding Pseudo function.

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt (fromInt)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx)
import Pickles.Field (StepField, WrapField)
import Pickles.Pseudo (choose, oneHotVector)
import Pickles.Pseudo as Pseudo
import Pickles.Sideload.VerificationKey (compileDummy)
import Pickles.Step.FinalizeOtherProof as FOP
import Pickles.VerificationKey (chooseKey)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_, exists, label)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- one_hot_vector N1
--------------------------------------------------------------------------------

-- | Takes 1 public input field (the index to select).
oneHotN1Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
oneHotN1Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n1" $ (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  pure unit

compileOneHotN1Step :: CompiledCircuit StepField
compileOneHotN1Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN1Circuit
  Kimchi.initialState

compileOneHotN1Wrap :: CompiledCircuit WrapField
compileOneHotN1Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN1Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- one_hot_vector N3
--------------------------------------------------------------------------------

-- | Takes 1 public input field (the index to select).
oneHotN3Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
oneHotN3Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n3" $ (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  pure unit

compileOneHotN3Step :: CompiledCircuit StepField
compileOneHotN3Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN3Circuit
  Kimchi.initialState

compileOneHotN3Wrap :: CompiledCircuit WrapField
compileOneHotN3Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN3Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- pseudo_mask N1
--------------------------------------------------------------------------------

pseudoMaskN1Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 2 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
pseudoMaskN1Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- label "pseudo_mask_n1" $ choose bits ((at 1 :< Vector.nil)) identity
  pure unit

compilePseudoMaskN1Step :: CompiledCircuit StepField
compilePseudoMaskN1Step = compilePure (Proxy @(Vector 2 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN1Circuit
  Kimchi.initialState

compilePseudoMaskN1Wrap :: CompiledCircuit WrapField
compilePseudoMaskN1Wrap = compilePure (Proxy @(Vector 2 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN1Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- pseudo_mask N3
--------------------------------------------------------------------------------

pseudoMaskN3Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 4 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
pseudoMaskN3Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  _ <- label "pseudo_mask_n3" $ choose bits (at 1 :< at 2 :< at 3 :< Vector.nil) identity
  pure unit

compilePseudoMaskN3Step :: CompiledCircuit StepField
compilePseudoMaskN3Step = compilePure (Proxy @(Vector 4 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN3Circuit
  Kimchi.initialState

compilePseudoMaskN3Wrap :: CompiledCircuit WrapField
compilePseudoMaskN3Wrap = compilePure (Proxy @(Vector 4 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN3Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- pseudo_choose N1 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN1Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
pseudoChooseN1Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- label "pseudo_choose_n1" $
    choose bits ((42 :< Vector.nil)) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN1Step :: CompiledCircuit StepField
compilePseudoChooseN1Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN1Circuit
  Kimchi.initialState

compilePseudoChooseN1Wrap :: CompiledCircuit WrapField
compilePseudoChooseN1Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN1Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- pseudo_choose N3 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN3Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
pseudoChooseN3Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  _ <- label "pseudo_choose_n3" $
    choose bits (13 :< 14 :< 15 :< Vector.nil) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN3Step :: CompiledCircuit StepField
compilePseudoChooseN3Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN3Circuit
  Kimchi.initialState

compilePseudoChooseN3Wrap :: CompiledCircuit WrapField
compilePseudoChooseN3Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN3Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- choose_key N1 (single branch, dummy VK, Wrap side only)
-- Matches OCaml Wrap_verifier.choose_key with 1 branch and all-constant VK.
-- OCaml generates 14 Generic gates from this.
--------------------------------------------------------------------------------

chooseKeyN1WrapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 1 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
chooseKeyN1WrapCircuit inputs = do
  let
    at = unsafeIdx inputs
    { x: F dummyX, y: F dummyY } = dummyVestaPt
    dummyPt = { x: const_ dummyX, y: const_ dummyY } :: AffinePoint (FVar WrapField)
    dummyVK =
      { sigmaComm: Vector.replicate dummyPt :: Vector 7 _
      , coefficientsComm: Vector.replicate dummyPt :: Vector 15 _
      , genericComm: dummyPt
      , psmComm: dummyPt
      , completeAddComm: dummyPt
      , mulComm: dummyPt
      , emulComm: dummyPt
      , endomulScalarComm: dummyPt
      }
  whichBranch <- label "one_hot" $ (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- chooseKey whichBranch (dummyVK :< Vector.nil)
  pure unit

compileChooseKeyN1Wrap :: CompiledCircuit WrapField
compileChooseKeyN1Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  chooseKeyN1WrapCircuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- Utils.ones_vector with length=16 — side-loaded ones-prefix mask.
-- Mirrors `Util.Step.ones_vector ~first_zero:x Nat.N16.n` from
-- `mina/src/lib/crypto/pickles/util.ml:51-66`. PS analog is
-- `Pickles.Step.FinalizeOtherProof.mkSideLoadedOnesPrefixMask`.
--------------------------------------------------------------------------------

utilsOnesVectorN16Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
utilsOnesVectorN16Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "ones_vector_n16" $ FOP.mkSideLoadedOnesPrefixMask (at 0)
  pure unit

compileUtilsOnesVectorN16Step :: CompiledCircuit StepField
compileUtilsOnesVectorN16Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  utilsOnesVectorN16Circuit
  Kimchi.initialState

compileUtilsOnesVectorN16Wrap :: CompiledCircuit WrapField
compileUtilsOnesVectorN16Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  utilsOnesVectorN16Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- One_hot_vector.of_index with length=17 — the side-loaded domain dispatch.
-- Mirrors `O.of_index log2_size ~length:(S max_n)` from
-- `step_verifier.ml:824` where `max_n = N16`. PS analog uses
-- `oneHotVector` with N=17 (= the type-level Vector size).
--------------------------------------------------------------------------------

oneHotN17Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
oneHotN17Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n17" $ (oneHotVector :: _ -> _ (Vector 17 _)) (at 0)
  pure unit

compileOneHotN17Step :: CompiledCircuit StepField
compileOneHotN17Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN17Circuit
  Kimchi.initialState

compileOneHotN17Wrap :: CompiledCircuit WrapField
compileOneHotN17Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN17Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- Pseudo.mask with length=17 over CONSTANT generators.
-- Mirrors the side-loaded FOP's `Pseudo.mask domainWhiches generators`.
-- The generators are constants (Field.of_int 0..16 as placeholders).
--------------------------------------------------------------------------------

pseudoMaskN17Circuit
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
pseudoMaskN17Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 17 _)) (at 0)
  let
    gens :: Vector 17 (FVar _)
    gens = map (\i -> const_ (fromBigInt (fromInt i)))
      ( 0 :< 1 :< 2 :< 3 :< 4 :< 5 :< 6 :< 7 :< 8 :< 9 :< 10 :< 11
          :< 12
          :< 13
          :< 14
          :< 15
          :< 16
          :< Vector.nil
      )
  _ <- label "pseudo_mask_n17" $ Pseudo.mask bits gens
  pure unit

compilePseudoMaskN17Step :: CompiledCircuit StepField
compilePseudoMaskN17Step = compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN17Circuit
  Kimchi.initialState

compilePseudoMaskN17Wrap :: CompiledCircuit WrapField
compilePseudoMaskN17Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN17Circuit
  Kimchi.initialState

--------------------------------------------------------------------------------
-- Side_loaded_verification_key.typ check (step circuit only).
-- Mirrors the OCaml `exists Side_loaded_verification_key.typ
-- ~compute:(fun () -> Side_loaded_verification_key.dummy)`. The PS
-- analog allocates a `Sideload.VerificationKey (FVar StepField) (BoolVar StepField)`
-- which fires the `CheckedType` instance: bool checks + exactly_one for
-- each One_hot vec, plus on-curve checks for the 23 wrap_index points.
--------------------------------------------------------------------------------

sideloadedVkTypStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m Unit
sideloadedVkTypStepCircuit _ = do
  _ <- label "sideloaded_vk_typ" $ exists (pure compileDummy)
  pure unit

compileSideloadedVkTypStep :: CompiledCircuit StepField
compileSideloadedVkTypStep = compilePure (Proxy @Unit) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  sideloadedVkTypStepCircuit
  Kimchi.initialState
