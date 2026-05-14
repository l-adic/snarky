module Snarky.Constraint.Kimchi
  ( KimchiConstraint(..)
  , KimchiGate
  , class KimchiVerify
  , eval
  , initialState
  , postCondition
  ) where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Array (all)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (over, un)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Data.UnionFind (equivalenceClasses)
import Data.Vector (Vector)
import Poseidon (class PoseidonField)
import Snarky.Backend.Builder (class CompileCircuit, class Finalizer, CircuitBuilderState, CircuitBuilderT, Labeled)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (class SolveCircuit, ProverT, throwProverError)
import Snarky.Backend.Prover as Prover
import Snarky.Circuit.CVar (Variable, v0)
import Snarky.Circuit.DSL (class BasicSystem, class ConstraintM, Basic(..), EvaluationError(..), FVar)
import Snarky.Constraint.Basic as Basic
import Snarky.Constraint.Kimchi.AddComplete (class AddCompleteVerifiable, AddComplete)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.EndoMul (EndoMul)
import Snarky.Constraint.Kimchi.EndoMul as EndoMul
import Snarky.Constraint.Kimchi.EndoScalar (EndoScalar)
import Snarky.Constraint.Kimchi.EndoScalar as EndoScalar
import Snarky.Constraint.Kimchi.GenericPlonk (class GenericPlonkVerifiable)
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (class PoseidonVerifiable, PoseidonConstraint)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, Rows, finalizeGateQueue, mkRawGeneric7Row, reduceAsBuilder, reduceAsProver, reduceToVariable)
import Snarky.Constraint.Kimchi.Reduction as Reduction
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, AuxState(..), KimchiRow, initialAuxState, toKimchiRows)
import Snarky.Constraint.Kimchi.VarBaseMul (class VarBaseMulVerifiable, VarBaseMul)
import Snarky.Constraint.Kimchi.VarBaseMul as VarBaseMul
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Utils (PostCondition)

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiAddComplete (AddComplete f)
  | KimchiPoseidon (PoseidonConstraint f)
  | KimchiVarBaseMul (VarBaseMul f)
  | KimchiEndoScalar (EndoScalar f)
  | KimchiEndoMul (EndoMul (FVar f))
  | KimchiRawGeneric7 (Vector 7 (FVar f))

data KimchiGate f
  = KimchiGatePlonk (Reduction.Rows f)
  | KimchiGateAddComplete (AddComplete.Rows f)
  | KimchiGatePoseidon (Poseidon.Rows f)
  | KimchiGateVarBaseMul (VarBaseMul.Rows f)
  | KimchiGateEndoScalar (EndoScalar.Rows f)
  | KimchiGateEndoMul (EndoMul.Rows f)
  | KimchiGateNoOp

instance ToKimchiRows f (KimchiGate f) where
  toKimchiRows = case _ of
    KimchiGatePlonk a -> toKimchiRows a
    KimchiGateAddComplete a -> toKimchiRows a
    KimchiGatePoseidon a -> toKimchiRows a
    KimchiGateVarBaseMul a -> toKimchiRows a
    KimchiGateEndoScalar a -> toKimchiRows a
    KimchiGateEndoMul a -> toKimchiRows a
    KimchiGateNoOp -> []

instance PrimeField f => Finalizer (KimchiGate f) (AuxState f) where
  finalize s =
    let
      mRow = finalizeGateQueue (un AuxState s.aux)
      lbl = s.labelStack
    in
      s
        { constraints = maybe s.constraints (\r -> s.constraints `Array.snoc` { constraint: KimchiGatePlonk r, context: lbl }) mRow
        , aux = over AuxState
            ( \st ->
                st
                  { queuedGenericGate = Nothing
                  }
            )
            s.aux
        }

reduceRawGeneric7
  :: forall n f
   . PlonkReductionM n f
  => Vector 7 (FVar f)
  -> n (Rows f)
reduceRawGeneric7 vs = do
  varsReduced <- traverse reduceToVariable vs
  pure (mkRawGeneric7Row varsReduced)

instance PoseidonField f => CompileCircuit f (KimchiGate f) (KimchiConstraint f) (AuxState f)

instance
  ( PoseidonField f
  ) =>
  ConstraintM (CircuitBuilderT (KimchiGate f) (AuxState f)) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> go AddComplete.reduce KimchiGateAddComplete c
    KimchiPoseidon c -> go Poseidon.reduce KimchiGatePoseidon c
    KimchiBasic c -> go GenericPlonk.reduce (const KimchiGateNoOp) c
    KimchiVarBaseMul c -> go VarBaseMul.reduce KimchiGateVarBaseMul c
    KimchiEndoScalar c -> go EndoScalar.reduce KimchiGateEndoScalar c
    KimchiEndoMul c -> go EndoMul.reduce KimchiGateEndoMul c
    KimchiRawGeneric7 vs -> go reduceRawGeneric7 KimchiGatePlonk vs
    where
    go
      :: forall a c m
       . Monad m
      => (forall n. PlonkReductionM n f => c -> n a)
      -> (a -> KimchiGate f)
      -> c
      -> CircuitBuilderT (KimchiGate f) (AuxState f) m Unit
    go reducer wrap c = do
      s <- CircuitBuilder.getState
      let
        Tuple rows res = reduceAsBuilder
          { nextVariable: s.nextVar
          , aux: s.aux
          }
          (reducer c)
        lbl = s.labelStack

        labelGate :: forall g. g -> Labeled g
        labelGate g = { constraint: g, context: lbl }
      CircuitBuilder.putState s
        { nextVar = res.nextVariable
        , constraints = s.constraints <> map (labelGate <<< KimchiGatePlonk) res.constraints `Array.snoc` labelGate (wrap rows)
        , aux = res.aux
        }

instance (KimchiVerify f f') => SolveCircuit f (KimchiConstraint f)

instance (KimchiVerify f f') => ConstraintM (ProverT f) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> goDebug AddComplete.reduce AddComplete.eval c
    KimchiPoseidon c -> goDebug Poseidon.reduce Poseidon.eval c
    KimchiBasic c -> goBasic c
    KimchiVarBaseMul c -> goDebug VarBaseMul.reduce VarBaseMul.eval c
    KimchiEndoScalar c -> goDebug EndoScalar.reduce EndoScalar.eval c
    KimchiEndoMul c -> goDebug EndoMul.reduce (EndoMul.eval @f @f') c
    KimchiRawGeneric7 vs -> goDebug reduceRawGeneric7 (\_ _ -> pure true) vs
    where
    -- Reduce and optionally debug-check the gate equation
    goDebug
      :: forall c g m
       . Monad m
      => ToKimchiRows f g
      => (forall n. PlonkReductionM n f => c -> n g)
      -> ((Variable -> Except EvaluationError f) -> g -> Except EvaluationError Boolean)
      -> c
      -> ProverT f m Unit
    goDebug reducer evalGate c = do
      s <- Prover.getState
      case reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (reducer c) of
        Left e -> throwProverError e
        Right (Tuple rows res) -> do
          Prover.putState $ s { assignments = res.assignments, nextVar = res.nextVariable }
          when s.debug do
            let lookupVar v = maybe (throwError $ MissingVariable v) pure (Map.lookup v res.assignments)
            case runExcept (evalGate lookupVar rows) of
              Left e -> throwProverError e
              Right false ->
                let
                  kimchiRows = toKimchiRows rows :: Array (KimchiRow f)
                  gateKind = maybe "Unknown" (show <<< _.kind) (Array.head kimchiRows)
                  nRows = Array.length kimchiRows
                in
                  throwProverError $ FailedAssertion
                    $ gateKind <> " gate check failed (" <> show nRows <> " rows)"
              Right true -> pure unit

    -- Basic constraints use debugCheck for richer error messages (e.g. "R1CS failed: 42 * 7 != 293")
    goBasic :: forall m. Monad m => Basic f -> ProverT f m Unit
    goBasic c = do
      s <- Prover.getState
      case reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (GenericPlonk.reduce c) of
        Left e -> throwProverError e
        Right (Tuple _ res) -> do
          Prover.putState $ s { assignments = res.assignments, nextVar = res.nextVariable }
          when s.debug do
            case Basic.debugCheck (flip Map.lookup res.assignments) c of
              Nothing -> pure unit
              Just e -> throwProverError e

initialState :: forall f. CircuitBuilderState (KimchiGate f) (AuxState f)
initialState =
  { nextVar: v0
  , constraints: mempty
  , publicInputs: mempty
  , aux: initialAuxState
  , labelStack: []
  , varMetadata: Map.empty
  }

eval
  :: forall f f' m
   . KimchiVerify f f'
  => Monad m
  => (Variable -> m f)
  -> KimchiGate f
  -> m Boolean
eval lookup = case _ of
  KimchiGatePlonk c -> GenericPlonk.eval lookup c
  KimchiGateAddComplete c -> AddComplete.eval lookup c
  KimchiGatePoseidon c -> Poseidon.eval lookup c
  KimchiGateVarBaseMul c -> VarBaseMul.eval lookup c
  KimchiGateEndoScalar c -> EndoScalar.eval lookup c
  KimchiGateEndoMul c -> EndoMul.eval @f @f' lookup c
  KimchiGateNoOp -> pure true

postCondition
  :: forall f
   . PrimeField f
  => PostCondition f (KimchiGate f) (AuxState f)
postCondition lookup { aux: AuxState { wireState: { unionFind } } } = do
  classes <- for (equivalenceClasses unionFind) \_class -> do
    values <- traverse lookup _class
    pure $ Set.fromFoldable values
  pure $ all (\s -> Set.size s == 1) classes

class
  ( HasEndo f f'
  , HasEndo f' f
  , GenericPlonkVerifiable f
  , AddCompleteVerifiable f
  , PoseidonVerifiable f
  , VarBaseMulVerifiable f
  ) <=
  KimchiVerify f f'
  | f -> f'

instance KimchiVerify Pallas.ScalarField Vesta.ScalarField
instance KimchiVerify Vesta.ScalarField Pallas.ScalarField

instance PrimeField f => BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  square a c = KimchiBasic $ Square a c
  boolean = KimchiBasic <<< Boolean
