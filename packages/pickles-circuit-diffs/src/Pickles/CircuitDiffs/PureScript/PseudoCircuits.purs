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
import Effect (Effect)
import JS.BigInt (fromInt)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, unsafeIdx)
import Pickles.Field (StepField, WrapField)
import Pickles.Pseudo (choose, oneHotVector)
import Pickles.Pseudo as Pseudo
import Pickles.Sideload.VerificationKey (compileDummy)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.Step.FinalizeOtherProof as FOP
import Pickles.Types (ChunkedCommitment(..))
import Pickles.VerificationKey (chooseKey)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F(..), FVar, Snarky, const_, exists, label)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- one_hot_vector N1
--------------------------------------------------------------------------------

-- | Takes 1 public input field (the index to select).
oneHotN1Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN1Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n1" $ (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  pure unit

compileOneHotN1Step :: Effect (CompiledCircuit StepField)
compileOneHotN1Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN1Circuit

compileOneHotN1Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN1Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN1Circuit

--------------------------------------------------------------------------------
-- one_hot_vector N3
--------------------------------------------------------------------------------

-- | Takes 1 public input field (the index to select).
oneHotN3Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN3Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n3" $ (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  pure unit

compileOneHotN3Step :: Effect (CompiledCircuit StepField)
compileOneHotN3Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN3Circuit

compileOneHotN3Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN3Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN3Circuit

--------------------------------------------------------------------------------
-- pseudo_mask N1
--------------------------------------------------------------------------------

pseudoMaskN1Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 2 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
pseudoMaskN1Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- label "pseudo_mask_n1" $ choose bits ((at 1 :< Vector.nil)) identity
  pure unit

compilePseudoMaskN1Step :: Effect (CompiledCircuit StepField)
compilePseudoMaskN1Step = compile noAdvice (Proxy @(Vector 2 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN1Circuit

compilePseudoMaskN1Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN1Wrap = compile noAdvice (Proxy @(Vector 2 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN1Circuit

--------------------------------------------------------------------------------
-- pseudo_mask N3
--------------------------------------------------------------------------------

pseudoMaskN3Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 4 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
pseudoMaskN3Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  _ <- label "pseudo_mask_n3" $ choose bits (at 1 :< at 2 :< at 3 :< Vector.nil) identity
  pure unit

compilePseudoMaskN3Step :: Effect (CompiledCircuit StepField)
compilePseudoMaskN3Step = compile noAdvice (Proxy @(Vector 4 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN3Circuit

compilePseudoMaskN3Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN3Wrap = compile noAdvice (Proxy @(Vector 4 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN3Circuit

--------------------------------------------------------------------------------
-- pseudo_choose N1 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN1Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
pseudoChooseN1Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- label "pseudo_choose_n1" $
    choose bits ((42 :< Vector.nil)) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN1Step :: Effect (CompiledCircuit StepField)
compilePseudoChooseN1Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN1Circuit

compilePseudoChooseN1Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoChooseN1Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN1Circuit

--------------------------------------------------------------------------------
-- pseudo_choose N3 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN3Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
pseudoChooseN3Circuit inputs = do
  let at = unsafeIdx inputs
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) (at 0)
  _ <- label "pseudo_choose_n3" $
    choose bits (13 :< 14 :< 15 :< Vector.nil) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN3Step :: Effect (CompiledCircuit StepField)
compilePseudoChooseN3Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN3Circuit

compilePseudoChooseN3Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoChooseN3Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN3Circuit

--------------------------------------------------------------------------------
-- choose_key N1 (single branch, dummy VK, Wrap side only)
-- Matches OCaml Wrap_verifier.choose_key with 1 branch and all-constant VK.
-- OCaml generates 14 Generic gates from this.
--------------------------------------------------------------------------------

chooseKeyN1WrapCircuit
  :: forall r
   . PrimeField WrapField
  => Vector 1 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
chooseKeyN1WrapCircuit inputs = do
  let
    at = unsafeIdx inputs
    AffinePoint { x: F dummyX, y: F dummyY } = dummyVestaPt
    dummyPt = AffinePoint { x: const_ dummyX, y: const_ dummyY } :: AffinePoint (FVar WrapField)
    dummyPtChunks = ChunkedCommitment (Vector.singleton dummyPt)
    dummyVK =
      { sigmaComm: Vector.replicate dummyPtChunks :: Vector 7 _
      , coefficientsComm: Vector.replicate dummyPtChunks :: Vector 15 _
      , genericComm: dummyPtChunks
      , psmComm: dummyPtChunks
      , completeAddComm: dummyPtChunks
      , mulComm: dummyPtChunks
      , emulComm: dummyPtChunks
      , endomulScalarComm: dummyPtChunks
      }
  whichBranch <- label "one_hot" $ (oneHotVector :: _ -> _ (Vector 1 _)) (at 0)
  _ <- chooseKey whichBranch (dummyVK :< Vector.nil)
  pure unit

compileChooseKeyN1Wrap :: Effect (CompiledCircuit WrapField)
compileChooseKeyN1Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  chooseKeyN1WrapCircuit

--------------------------------------------------------------------------------
-- Utils.ones_vector with length=16 — side-loaded ones-prefix mask.
-- Mirrors `Util.Step.ones_vector ~first_zero:x Nat.N16.n` from
-- `mina/src/lib/crypto/pickles/util.ml:51-66`. PS analog is
-- `Pickles.Step.FinalizeOtherProof.mkSideLoadedOnesPrefixMask`.
--------------------------------------------------------------------------------

utilsOnesVectorN16Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
utilsOnesVectorN16Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "ones_vector_n16" $ FOP.mkSideLoadedOnesPrefixMask (at 0)
  pure unit

compileUtilsOnesVectorN16Step :: Effect (CompiledCircuit StepField)
compileUtilsOnesVectorN16Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  utilsOnesVectorN16Circuit

compileUtilsOnesVectorN16Wrap :: Effect (CompiledCircuit WrapField)
compileUtilsOnesVectorN16Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  utilsOnesVectorN16Circuit

--------------------------------------------------------------------------------
-- One_hot_vector.of_index with length=17 — the side-loaded domain dispatch.
-- Mirrors `O.of_index log2_size ~length:(S max_n)` from
-- `step_verifier.ml:824` where `max_n = N16`. PS analog uses
-- `oneHotVector` with N=17 (= the type-level Vector size).
--------------------------------------------------------------------------------

oneHotN17Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN17Circuit inputs = do
  let at = unsafeIdx inputs
  _ <- label "one_hot_n17" $ (oneHotVector :: _ -> _ (Vector 17 _)) (at 0)
  pure unit

compileOneHotN17Step :: Effect (CompiledCircuit StepField)
compileOneHotN17Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN17Circuit

compileOneHotN17Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN17Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN17Circuit

--------------------------------------------------------------------------------
-- Pseudo.mask with length=17 over CONSTANT generators.
-- Mirrors the side-loaded FOP's `Pseudo.mask domainWhiches generators`.
-- The generators are constants (Field.of_int 0..16 as placeholders).
--------------------------------------------------------------------------------

pseudoMaskN17Circuit
  :: forall f r
   . PrimeField f
  => PrimeField f
  => Vector 1 (FVar f)
  -> Snarky f (KimchiConstraint f) r Unit
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

compilePseudoMaskN17Step :: Effect (CompiledCircuit StepField)
compilePseudoMaskN17Step = compile noAdvice (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN17Circuit

compilePseudoMaskN17Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN17Wrap = compile noAdvice (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN17Circuit

--------------------------------------------------------------------------------
-- Side_loaded_verification_key.typ check (step circuit only).
-- Mirrors the OCaml `exists Side_loaded_verification_key.typ
-- ~compute:(fun () -> Side_loaded_verification_key.dummy)`. The PS
-- analog allocates a `Sideload.VerificationKey (FVar StepField) (BoolVar StepField)`
-- which fires the `CheckedType` instance: bool checks + exactly_one for
-- each One_hot vec, plus on-curve checks for the 23 wrap_index points.
--------------------------------------------------------------------------------

sideloadedVkTypStepCircuit
  :: forall r
   . PrimeField StepField
  => Unit
  -> Snarky StepField (KimchiConstraint StepField) r Unit
sideloadedVkTypStepCircuit _ = do
  _ <- label "sideloaded_vk_typ" $ exists (pure (compileDummy :: SLVK.VerificationKey 1 (F StepField) Boolean))
  pure unit

compileSideloadedVkTypStep :: Effect (CompiledCircuit StepField)
compileSideloadedVkTypStep = compile noAdvice (Proxy @Unit) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  sideloadedVkTypStepCircuit
