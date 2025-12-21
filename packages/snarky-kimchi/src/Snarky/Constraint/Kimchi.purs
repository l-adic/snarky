module Snarky.Constraint.Kimchi
  ( KimchiConstraint(..)
  , KimchiGate(..)
  , eval
  , AuxState(..)
  , initialState
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Newtype (class Newtype, un)
import Data.Tuple (Tuple(..))
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Builder (CircuitBuilderT, CircuitBuilderState, appendConstraint)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (ProverT, throwProverError)
import Snarky.Backend.Prover as Prover
import Snarky.Circuit.CVar (Variable, v0)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem, Basic(..))
import Snarky.Constraint.Kimchi.AddComplete (AddComplete)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.GenericPlonk (reduceBasic)
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (PoseidonConstraint)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
import Snarky.Constraint.Kimchi.Reduction (reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Constraint.Kimchi.Wire (KimchiWireRow, emptyKimchiWireState)
import Snarky.Curves.Class (class PrimeField)

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiPlonk (GenericPlonkConstraint f)
  | KimchiAddComplete (AddComplete f)
  | KimchiPoseidon (PoseidonConstraint f)

data KimchiGate f
  = KimchiGatePlonk (GenericPlonkConstraint f)
  | KimchiGateAddComplete (AddComplete f)
  | KimchiGatePoseidon (PoseidonConstraint f)

newtype AuxState f = AuxState
  { wireState :: KimchiWireRow f
  }

derive instance Newtype (AuxState f) _

initialAuxState :: forall f. AuxState f
initialAuxState = AuxState
  { wireState: emptyKimchiWireState
  }

instance PrimeField f => ConstraintM (CircuitBuilderT (KimchiGate f) (AuxState f)) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> appendConstraint (KimchiGateAddComplete c)
    KimchiPoseidon c -> appendConstraint (KimchiGatePoseidon c)
    KimchiPlonk c -> appendConstraint (KimchiGatePlonk c)
    KimchiBasic c -> do
      s <- CircuitBuilder.getState
      let
        Tuple _ res = reduceAsBuilder
          { nextVariable: s.nextVar
          , wireState: (un AuxState s.aux).wireState
          }
          (reduceBasic c)
      CircuitBuilder.putState s
        { nextVar = res.nextVariable
        , constraints = s.constraints <> map KimchiGatePlonk res.constraints
        , aux = AuxState { wireState: res.wireState }
        }

instance PrimeField f => ConstraintM (ProverT f) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiBasic c -> do
      s <- Prover.getState
      case reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (reduceBasic c) of
        Left e -> throwProverError e
        Right (Tuple _ res) -> Prover.putState $ s { assignments = res.assignments, nextVar = res.nextVariable }
    _ -> pure unit

initialState :: forall f. CircuitBuilderState (KimchiGate f) (AuxState f)
initialState =
  { nextVar: v0
  , constraints: mempty
  , publicInputs: mempty
  , aux: initialAuxState
  }

eval
  :: forall f m
   . PoseidonField f
  => PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> KimchiGate f
  -> m Boolean
eval lookup = case _ of
  KimchiGatePlonk c -> GenericPlonk.eval lookup c
  KimchiGateAddComplete c -> AddComplete.eval lookup c
  KimchiGatePoseidon c -> Poseidon.eval lookup c

instance PrimeField f => BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  boolean = KimchiBasic <<< Boolean