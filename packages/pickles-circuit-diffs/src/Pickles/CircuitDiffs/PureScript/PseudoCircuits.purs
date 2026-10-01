module Pickles.CircuitDiffs.PureScript.PseudoCircuits
  ( compileChooseKeyN1Wrap
  , compileOneHotN1Step
  , compileOneHotN1Wrap
  , compileOneHotN3Step
  , compileOneHotN3Wrap
  , compilePseudoToDomainWrap
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
-- | Each circuit takes its typed input and calls the corresponding Pseudo function.

import Prelude

import Data.Fin (reflectFinite)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import JS.BigInt (fromInt)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization.FFI as LinFFI
import Pickles.ProofsVerified (wrapDomainShifts)
import Pickles.Pseudo (choose, oneHotVector)
import Pickles.Pseudo as Pseudo
import Pickles.Sideload.VerificationKey (compileDummy)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.Step.FinalizeOtherProof as FOP
import Pickles.Types (ChunkedCommitment(..))
import Pickles.VerificationKey (chooseKey)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F(..), FVar, Snarky, UnChecked(..), const_, exists, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, label)
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
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN1Circuit index = do
  _ <- label "one_hot_n1" $ (oneHotVector :: _ -> _ (Vector 1 _)) index
  pure unit

compileOneHotN1Step :: Effect (CompiledCircuit StepField)
compileOneHotN1Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN1Circuit

compileOneHotN1Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN1Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN1Circuit

--------------------------------------------------------------------------------
-- one_hot_vector N3
--------------------------------------------------------------------------------

-- | Takes 1 public input field (the index to select).
oneHotN3Circuit
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN3Circuit index = do
  _ <- label "one_hot_n3" $ (oneHotVector :: _ -> _ (Vector 3 _)) index
  pure unit

compileOneHotN3Step :: Effect (CompiledCircuit StepField)
compileOneHotN3Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN3Circuit

compileOneHotN3Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN3Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN3Circuit

--------------------------------------------------------------------------------
-- to_domain over the three wrap domains
--------------------------------------------------------------------------------

-- | `pseudo_to_domain_wrap_circuit`'s input: the domain index and `zeta`.
newtype PseudoToDomainInput f = PseudoToDomainInput
  { index :: f
  , zeta :: f
  }

-- | The wire order.
type PseudoToDomainTuple f = Tuple2 f f

instance CircuitType f fa fv => CircuitType f (PseudoToDomainInput fa) (PseudoToDomainInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PseudoToDomainTuple fa))
  valueToFields = genericValueToFields <<< toDomainTuple
  fieldsToValue = toDomainInput <<< genericFieldsToValue
  varToFields = genericVarToFields @(PseudoToDomainTuple fa) <<< toDomainTuple
  fieldsToVar = toDomainInput <<< genericFieldsToVar @(PseudoToDomainTuple fa)

toDomainTuple :: forall f. PseudoToDomainInput f -> PseudoToDomainTuple f
toDomainTuple (PseudoToDomainInput i) = tuple2 i.index i.zeta

toDomainInput :: forall f. PseudoToDomainTuple f -> PseudoToDomainInput f
toDomainInput = uncurry2 \index zeta -> PseudoToDomainInput { index, zeta }

-- | The one-hot of the index, then the selected wrap domain's vanishing polynomial at `zeta`,
-- | as `wrapMain` selects each slot's finalize domain.
pseudoToDomainWrapCircuit
  :: forall r
   . UnChecked (PseudoToDomainInput (FVar WrapField))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
pseudoToDomainWrapCircuit (UnChecked (PseudoToDomainInput i)) = do
  which <- Pseudo.oneHotVector @3 i.index
  domain <- Pseudo.toDomain @16
    { shifts: wrapDomainShifts
    , domainGenerator: LinFFI.domainGenerator @WrapField
    }
    which
    (reflectFinite @13 :< reflectFinite @14 :< reflectFinite @15 :< Vector.nil)
  _ <- label "pseudo_to_domain" $ domain.vanishingPolynomial i.zeta
  pure unit

compilePseudoToDomainWrap :: Effect (CompiledCircuit WrapField)
compilePseudoToDomainWrap = compile noAdvice (Proxy @(UnChecked (PseudoToDomainInput (F WrapField)))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoToDomainWrapCircuit

--------------------------------------------------------------------------------
-- pseudo_mask N1, N3
--------------------------------------------------------------------------------

-- | `pseudo_mask_n{1,3}`'s input: the index to select, then the `n` values to mask.
newtype PseudoMaskInput n f = PseudoMaskInput
  { index :: f
  , values :: Vector n f
  }

-- | The wire order.
type PseudoMaskTuple n f = Tuple2 f (Vector n f)

instance (Reflectable n Int, CircuitType f fa fv) => CircuitType f (PseudoMaskInput n fa) (PseudoMaskInput n fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PseudoMaskTuple n fa))
  valueToFields = genericValueToFields <<< maskTuple
  fieldsToValue = maskInput <<< genericFieldsToValue
  varToFields = genericVarToFields @(PseudoMaskTuple n fa) <<< maskTuple
  fieldsToVar = maskInput <<< genericFieldsToVar @(PseudoMaskTuple n fa)

maskTuple :: forall n f. PseudoMaskInput n f -> PseudoMaskTuple n f
maskTuple (PseudoMaskInput i) = tuple2 i.index i.values

maskInput :: forall n f. PseudoMaskTuple n f -> PseudoMaskInput n f
maskInput = uncurry2 \index values -> PseudoMaskInput { index, values }

pseudoMaskN1Circuit
  :: forall f r
   . PrimeField f
  => UnChecked (PseudoMaskInput 1 (FVar f))
  -> Snarky f (KimchiConstraint f) r Unit
pseudoMaskN1Circuit (UnChecked (PseudoMaskInput i)) = do
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) i.index
  _ <- label "pseudo_mask_n1" $ choose bits i.values identity
  pure unit

compilePseudoMaskN1Step :: Effect (CompiledCircuit StepField)
compilePseudoMaskN1Step = compile noAdvice (Proxy @(UnChecked (PseudoMaskInput 1 (F StepField)))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN1Circuit

compilePseudoMaskN1Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN1Wrap = compile noAdvice (Proxy @(UnChecked (PseudoMaskInput 1 (F WrapField)))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN1Circuit

pseudoMaskN3Circuit
  :: forall f r
   . PrimeField f
  => UnChecked (PseudoMaskInput 3 (FVar f))
  -> Snarky f (KimchiConstraint f) r Unit
pseudoMaskN3Circuit (UnChecked (PseudoMaskInput i)) = do
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) i.index
  _ <- label "pseudo_mask_n3" $ choose bits i.values identity
  pure unit

compilePseudoMaskN3Step :: Effect (CompiledCircuit StepField)
compilePseudoMaskN3Step = compile noAdvice (Proxy @(UnChecked (PseudoMaskInput 3 (F StepField)))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN3Circuit

compilePseudoMaskN3Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN3Wrap = compile noAdvice (Proxy @(UnChecked (PseudoMaskInput 3 (F WrapField)))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN3Circuit

--------------------------------------------------------------------------------
-- pseudo_choose N1 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN1Circuit
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
pseudoChooseN1Circuit index = do
  bits <- (oneHotVector :: _ -> _ (Vector 1 _)) index
  _ <- label "pseudo_choose_n1" $
    choose bits ((42 :< Vector.nil)) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN1Step :: Effect (CompiledCircuit StepField)
compilePseudoChooseN1Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN1Circuit

compilePseudoChooseN1Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoChooseN1Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN1Circuit

--------------------------------------------------------------------------------
-- pseudo_choose N3 (constant targets)
--------------------------------------------------------------------------------

pseudoChooseN3Circuit
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
pseudoChooseN3Circuit index = do
  bits <- (oneHotVector :: _ -> _ (Vector 3 _)) index
  _ <- label "pseudo_choose_n3" $
    choose bits (13 :< 14 :< 15 :< Vector.nil) (\x -> const_ (fromBigInt (fromInt x)))
  pure unit

compilePseudoChooseN3Step :: Effect (CompiledCircuit StepField)
compilePseudoChooseN3Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoChooseN3Circuit

compilePseudoChooseN3Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoChooseN3Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN3Circuit

--------------------------------------------------------------------------------
-- choose_key N1 (single branch, dummy VK, Wrap side only)
-- Matches OCaml Wrap_verifier.choose_key with 1 branch and all-constant VK.
-- OCaml generates 14 Generic gates from this.
--------------------------------------------------------------------------------

chooseKeyN1WrapCircuit
  :: forall r
   . PrimeField WrapField
  => FVar WrapField
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
chooseKeyN1WrapCircuit branch = do
  let
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
  whichBranch <- label "one_hot" $ (oneHotVector :: _ -> _ (Vector 1 _)) branch
  _ <- chooseKey whichBranch (dummyVK :< Vector.nil)
  pure unit

compileChooseKeyN1Wrap :: Effect (CompiledCircuit WrapField)
compileChooseKeyN1Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
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
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
utilsOnesVectorN16Circuit firstZero = do
  _ <- label "ones_vector_n16" $ FOP.mkSideLoadedOnesPrefixMask firstZero
  pure unit

compileUtilsOnesVectorN16Step :: Effect (CompiledCircuit StepField)
compileUtilsOnesVectorN16Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  utilsOnesVectorN16Circuit

compileUtilsOnesVectorN16Wrap :: Effect (CompiledCircuit WrapField)
compileUtilsOnesVectorN16Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
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
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
oneHotN17Circuit index = do
  _ <- label "one_hot_n17" $ (oneHotVector :: _ -> _ (Vector 17 _)) index
  pure unit

compileOneHotN17Step :: Effect (CompiledCircuit StepField)
compileOneHotN17Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  oneHotN17Circuit

compileOneHotN17Wrap :: Effect (CompiledCircuit WrapField)
compileOneHotN17Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN17Circuit

--------------------------------------------------------------------------------
-- Pseudo.mask with length=17 over CONSTANT generators.
-- Mirrors the side-loaded FOP's `Pseudo.mask domainWhiches generators`.
-- The generators are constants (Field.of_int 0..16 as placeholders).
--------------------------------------------------------------------------------

pseudoMaskN17Circuit
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r Unit
pseudoMaskN17Circuit index = do
  bits <- (oneHotVector :: _ -> _ (Vector 17 _)) index
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
compilePseudoMaskN17Step = compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  pseudoMaskN17Circuit

compilePseudoMaskN17Wrap :: Effect (CompiledCircuit WrapField)
compilePseudoMaskN17Wrap = compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
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
