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
import Data.Maybe (maybe)
import Data.Newtype (class Newtype, un)
import Data.Tuple (Tuple(..))
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Builder (class Finalizer, CircuitBuilderT, CircuitBuilderState)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (ProverT, throwProverError)
import Snarky.Backend.Prover as Prover
import Snarky.Circuit.CVar (Variable, v0)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Basic (class BasicSystem, Basic(..))
import Snarky.Constraint.Kimchi.AddComplete (AddComplete, class AddCompleteVerifiable)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.EndoScale (EndoScale)
import Snarky.Constraint.Kimchi.EndoScale as EndoScale
import Snarky.Constraint.Kimchi.GenericPlonk (class GenericPlonkVerifiable)
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (PoseidonConstraint, class PoseidonVerifiable)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addGenericPlonkConstraint, finalizeGateQueue, reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.VarBaseMul (class VarBaseMulVerifiable, VarBaseMul)
import Snarky.Constraint.Kimchi.VarBaseMul as VarBaseMul
import Snarky.Constraint.Kimchi.Wire (KimchiWireRow, KimchiRow, emptyKimchiWireState)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector)

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiAddComplete (AddComplete f)
  | KimchiPoseidon (PoseidonConstraint f)
  | KimchiVarBaseMul (VarBaseMul (FVar f))
  | KimchiEndoScale (EndoScale f)

data KimchiGate f
  = KimchiGatePlonk (KimchiRow f)
  | KimchiGateAddComplete (KimchiRow f)
  | KimchiGatePoseidon (Vector 12 (KimchiRow f))
  | KimchiGateVarBaseMul (Array (Vector 2 (KimchiRow f)))
  | KimchiGateEndoScale (Vector 8 (KimchiRow f))

newtype AuxState f = AuxState
  { wireState :: KimchiWireRow f
  }

instance PrimeField f => Finalizer (KimchiGate f) (AuxState f) where
  finalize s =
    let
      Tuple mRow ws' = finalizeGateQueue (un AuxState s.aux).wireState
    in
      s
        { constraints = maybe s.constraints (\r -> s.constraints `Array.snoc` KimchiGatePlonk r) mRow
        , aux = AuxState
            { wireState: ws'
            }
        }

derive instance Newtype (AuxState f) _

initialAuxState :: forall f. AuxState f
initialAuxState = AuxState
  { wireState: emptyKimchiWireState
  }

instance
  ( PrimeField f
  , PoseidonField f
  ) =>
  ConstraintM (CircuitBuilderT (KimchiGate f) (AuxState f)) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> go AddComplete.reduce KimchiGateAddComplete c
    KimchiPoseidon c -> go Poseidon.reduce KimchiGatePoseidon c
    -- this one is special :/
    KimchiBasic c -> do
      s <- CircuitBuilder.getState
      let
        Tuple _ res = reduceAsBuilder
          { nextVariable: s.nextVar
          , wireState: (un AuxState s.aux).wireState
          }
          (GenericPlonk.reduce c >>= maybe (pure unit) addGenericPlonkConstraint)
      CircuitBuilder.putState s
        { nextVar = res.nextVariable
        , constraints = s.constraints <> (KimchiGatePlonk <$> res.constraints)
        , aux = AuxState { wireState: res.wireState }
        }
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
        Tuple rows res = reduceAsBuilder
          { nextVariable: s.nextVar
          , wireState: (un AuxState s.aux).wireState
          }
          (reducer c)
      CircuitBuilder.putState s
        { nextVar = res.nextVariable
        , constraints = s.constraints <> (KimchiGatePlonk <$> res.constraints) `Array.snoc` (wrap rows)
        , aux = AuxState
            { wireState:
                res.wireState
            }
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

class (PrimeField f, GenericPlonkVerifiable f, AddCompleteVerifiable f, PoseidonVerifiable f, VarBaseMulVerifiable f) <= KimchiVerify f

instance KimchiVerify Pallas.BaseField
instance KimchiVerify Vesta.BaseField

instance PrimeField f => BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  boolean = KimchiBasic <<< Boolean