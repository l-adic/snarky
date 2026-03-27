module Pickles.CircuitDiffs.PureScript.PseudoCircuits
  ( compileOneHotN1Step
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
  ) where

-- | Pseudo module sub-circuit tests matching OCaml fixtures.
-- | Each circuit takes a flat input array and calls the corresponding Pseudo function.

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Pseudo (oneHotVector, choose)
import Pickles.Types (StepField, WrapField)
import JS.BigInt (fromInt)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, const_, label)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- one_hot_vector N1
--------------------------------------------------------------------------------

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
  oneHotN1Circuit Kimchi.initialState

compileOneHotN1Wrap :: CompiledCircuit WrapField
compileOneHotN1Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN1Circuit Kimchi.initialState

--------------------------------------------------------------------------------
-- one_hot_vector N3
--------------------------------------------------------------------------------

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
  oneHotN3Circuit Kimchi.initialState

compileOneHotN3Wrap :: CompiledCircuit WrapField
compileOneHotN3Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  oneHotN3Circuit Kimchi.initialState

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
  pseudoMaskN1Circuit Kimchi.initialState

compilePseudoMaskN1Wrap :: CompiledCircuit WrapField
compilePseudoMaskN1Wrap = compilePure (Proxy @(Vector 2 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN1Circuit Kimchi.initialState

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
  pseudoMaskN3Circuit Kimchi.initialState

compilePseudoMaskN3Wrap :: CompiledCircuit WrapField
compilePseudoMaskN3Wrap = compilePure (Proxy @(Vector 4 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoMaskN3Circuit Kimchi.initialState

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
  pseudoChooseN1Circuit Kimchi.initialState

compilePseudoChooseN1Wrap :: CompiledCircuit WrapField
compilePseudoChooseN1Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN1Circuit Kimchi.initialState

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
  pseudoChooseN3Circuit Kimchi.initialState

compilePseudoChooseN3Wrap :: CompiledCircuit WrapField
compilePseudoChooseN3Wrap = compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
  pseudoChooseN3Circuit Kimchi.initialState
