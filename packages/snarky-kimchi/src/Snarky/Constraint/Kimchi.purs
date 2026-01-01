module Snarky.Constraint.Kimchi
  ( AuxState(..)
  , KimchiConstraint(..)
  , KimchiGate
  , class KimchiVerify
  , eval
  , initialState
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, over, un)
import Data.Tuple (Tuple(..))
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Builder (class Finalizer, CircuitBuilderT, CircuitBuilderState)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (ProverT, throwProverError)
import Snarky.Backend.Prover as Prover
import Snarky.Circuit.CVar (Variable, v0)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem, Basic(..))
import Snarky.Constraint.Kimchi.AddComplete (AddComplete, class AddCompleteVerifiable)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.EndoScale (EndoScale)
import Snarky.Constraint.Kimchi.EndoScale as EndoScale
import Snarky.Constraint.Kimchi.GenericPlonk (class GenericPlonkVerifiable)
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (PoseidonConstraint, class PoseidonVerifiable)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, finalizeGateQueue, reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.Reduction as Reduction
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Constraint.Kimchi.VarBaseMul (class VarBaseMulVerifiable, VarBaseMul)
import Snarky.Constraint.Kimchi.VarBaseMul as VarBaseMul
import Snarky.Constraint.Kimchi.Wire (KimchiWireRow, emptyKimchiWireState)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiAddComplete (AddComplete f)
  | KimchiPoseidon (PoseidonConstraint f)
  | KimchiVarBaseMul (VarBaseMul f)
  | KimchiEndoScale (EndoScale f)

data KimchiGate f
  = KimchiGatePlonk (Reduction.Rows f)
  | KimchiGateAddComplete (AddComplete.Rows f)
  | KimchiGatePoseidon (Poseidon.Rows f)
  | KimchiGateVarBaseMul (VarBaseMul.Rows f)
  | KimchiGateEndoScale (EndoScale.Rows f)
  | KimchiGateNoOp

newtype AuxState f = AuxState
  { wireState :: KimchiWireRow f
  , queuedGenericGate :: Maybe (GenericPlonkConstraint f)
  }

instance PrimeField f => Finalizer (KimchiGate f) (AuxState f) where
  finalize s =
    let
      mRow = finalizeGateQueue (un AuxState s.aux)
    in
      s
        { constraints = maybe s.constraints (\r -> s.constraints `Array.snoc` KimchiGatePlonk r) mRow
        , aux = over AuxState
            ( \st ->
                st
                  { queuedGenericGate = Nothing
                  }
            )
            s.aux
        }

derive instance Newtype (AuxState f) _

initialAuxState :: forall f. AuxState f
initialAuxState = AuxState
  { wireState: emptyKimchiWireState
  , queuedGenericGate: Nothing
  }

instance
  ( PrimeField f
  , PoseidonField f
  ) =>
  ConstraintM (CircuitBuilderT (KimchiGate f) (AuxState f)) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> go AddComplete.reduce KimchiGateAddComplete c
    KimchiPoseidon c -> go Poseidon.reduce KimchiGatePoseidon c
    KimchiBasic c -> go GenericPlonk.reduce (const KimchiGateNoOp) c
    KimchiVarBaseMul c -> go VarBaseMul.reduce KimchiGateVarBaseMul c
    KimchiEndoScale c -> go EndoScale.reduce KimchiGateEndoScale c
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
        AuxState aux = s.aux
        Tuple rows res = reduceAsBuilder
          { nextVariable: s.nextVar
          , wireState: aux.wireState
          , queuedGenericGate: aux.queuedGenericGate
          }
          (reducer c)
      CircuitBuilder.putState s
        { nextVar = res.nextVariable
        , constraints = s.constraints <> (KimchiGatePlonk <$> res.constraints) `Array.snoc` (wrap rows)
        , aux = over AuxState
            ( \st ->
                st
                  { wireState = res.wireState
                  , queuedGenericGate = res.queuedGenericGate
                  }
            )
            s.aux
        }

instance (PrimeField f, PoseidonField f) => ConstraintM (ProverT f) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> go AddComplete.reduce c
    KimchiPoseidon c -> go Poseidon.reduce c
    KimchiBasic c -> go GenericPlonk.reduce c
    KimchiVarBaseMul c -> go VarBaseMul.reduce c
    KimchiEndoScale c -> go EndoScale.reduce c
    where
    go :: forall a c m. Monad m => (forall n. PlonkReductionM n f => c -> n a) -> c -> ProverT f m Unit
    go reducer c = do
      s <- Prover.getState
      case reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (reducer c) of
        Left e -> throwProverError e
        Right (Tuple _ res) -> Prover.putState $ s { assignments = res.assignments, nextVar = res.nextVariable }

initialState :: forall f. CircuitBuilderState (KimchiGate f) (AuxState f)
initialState =
  { nextVar: v0
  , constraints: mempty
  , publicInputs: mempty
  , aux: initialAuxState
  }

eval
  :: forall f m
   . KimchiVerify f
  => Applicative m
  => (Variable -> m f)
  -> KimchiGate f
  -> m Boolean
eval lookup = case _ of
  KimchiGatePlonk c -> GenericPlonk.eval lookup c
  KimchiGateAddComplete c -> AddComplete.eval lookup c
  KimchiGatePoseidon c -> Poseidon.eval lookup c
  KimchiGateVarBaseMul c -> VarBaseMul.eval lookup c
  KimchiGateEndoScale c -> EndoScale.eval lookup c
  KimchiGateNoOp -> pure true

class (PrimeField f, GenericPlonkVerifiable f, AddCompleteVerifiable f, PoseidonVerifiable f, VarBaseMulVerifiable f) <= KimchiVerify f

instance KimchiVerify Pallas.BaseField
instance KimchiVerify Vesta.BaseField

instance PrimeField f => BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  boolean = KimchiBasic <<< Boolean