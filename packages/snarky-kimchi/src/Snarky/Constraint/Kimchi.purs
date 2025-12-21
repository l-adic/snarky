module Snarky.Constraint.Kimchi
  ( KimchiConstraint(..)
  , KimchiGate(..)
  , eval
  ) where

import Prelude

import Data.Either (Either(..))
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Builder (CircuitBuilderT, appendConstraint)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (ProverT, throwProverError)
import Snarky.Backend.Prover as Prover
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem, Basic(..))
import Snarky.Constraint.Kimchi.AddComplete (AddComplete)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.GenericPlonk (GenericPlonkConstraint, reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (PoseidonConstraint)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
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

instance PrimeField f => ConstraintM (CircuitBuilderT (KimchiGate f) Unit) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiAddComplete c -> appendConstraint (KimchiGateAddComplete c)
    KimchiPoseidon c -> appendConstraint (KimchiGatePoseidon c)
    KimchiPlonk c -> appendConstraint (KimchiGatePlonk c)
    KimchiBasic c -> do
      s <- CircuitBuilder.getState
      let res = reduceAsBuilder { nextVariable: s.nextVar, constraints: [ c ] }
      CircuitBuilder.putState $ s { nextVar = res.nextVariable, constraints = s.constraints <> map KimchiGatePlonk res.constraints }

instance PrimeField f => ConstraintM (ProverT f) (KimchiConstraint f) where
  addConstraint' = case _ of
    KimchiBasic c -> do
      s <- Prover.getState
      case reduceAsProver [ c ] { assignments: s.assignments, nextVariable: s.nextVar } of
        Left e -> throwProverError e
        Right res -> Prover.putState $ s { assignments = res.assignments, nextVar = res.nextVariable }
    _ -> pure unit

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