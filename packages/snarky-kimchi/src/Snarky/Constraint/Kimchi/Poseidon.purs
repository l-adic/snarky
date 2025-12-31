module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , eval
  , reduce
  , class PoseidonVerifiable
  , verifyPoseidon
  ) where

import Prelude hiding (append)

import Data.FoldableWithIndex (traverseWithIndex_)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, getRoundConstants)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (Finite, getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector, append, flatten, head, nil, (!!), (:<))
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))

type PoseidonConstraint f =
  { state :: Vector 56 (Vector 3 (FVar f))
  }

class PoseidonField f <= PoseidonVerifiable f where
  verifyPoseidon :: Vector 12 (Vector 15 f) -> Boolean

instance PoseidonVerifiable Pallas.ScalarField where
  verifyPoseidon = verifyPallasPoseidon

instance PoseidonVerifiable Vesta.ScalarField where
  verifyPoseidon = verifyVestaPoseidon

eval
  :: forall f m
   . PrimeField f
  => PoseidonVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> PoseidonConstraint f
  -> m Boolean
eval lookup constraint = ado
  witness <- extractWitness constraint.state
  in verifyPoseidon witness
  where
  extractWitness
    :: Vector 56 (Vector 3 (FVar f))
    -> m (Vector 12 (Vector 15 f))
  extractWitness states = ado
    poseidonRows <- traverse extractRoundWitness stateGroups
    lastRow <- extractLastRow (head after)
    in poseidonRows `append` (lastRow :< nil)
    where
    { before, after } = Vector.splitAt @55 states
    stateGroups = Vector.chunks @5 before

  extractLastRow
    :: Vector 3 (FVar f)
    -> m (Vector 15 f)
  extractLastRow lastState = ado
    evaluated <- traverse (CVar.eval lookup) lastState
    in
      evaluated `append` Vector.generate (const zero)

  extractRoundWitness
    :: Vector 5 (Vector 3 (FVar f))
    -> m (Vector 15 f)
  extractRoundWitness roundStates = ado
    evaluatedStates <- traverse (traverse (CVar.eval lookup)) roundStates
    let
      s0 = evaluatedStates !! unsafeFinite 0
      s4 = evaluatedStates !! unsafeFinite 4
      s1 = evaluatedStates !! unsafeFinite 1
      s2 = evaluatedStates !! unsafeFinite 2
      s3 = evaluatedStates !! unsafeFinite 3
      reorderedStates = s0 :< s4 :< s1 :< s2 :< s3 :< nil
      witnessData = flatten reorderedStates
    in
      witnessData

reduce
  :: forall f m
   . PrimeField f
  => PoseidonField f
  => PlonkReductionM m f
  => PoseidonConstraint f
  -> m Unit
reduce c = do
  state <- traverse (traverse reduceToVariable) c.state
  let { before, after } = Vector.splitAt @55 state
  let rounds = Vector.chunks @5 before
  traverseWithIndex_ addRoundState rounds
  let lastRowVars = map Just (head after) `append` Vector.generate (const Nothing)
  addRow { kind: Zero, coeffs: Vector.generate (const zero), variables: lastRowVars }
  where
  addRoundState :: Finite 11 -> Vector 5 (Vector 3 Variable) -> m Unit
  addRoundState round s =
    let
      variables = map Just $
        (s !! unsafeFinite 0)
          `append` (s !! unsafeFinite 4)
          `append` (s !! unsafeFinite 1)
          `append` (s !! unsafeFinite 2)
          `append` (s !! unsafeFinite 3)
      coeffs =
        getRoundConstants (Proxy @f) (getFinite round)
          `append` getRoundConstants (Proxy @f) (getFinite round + 1)
          `append` getRoundConstants (Proxy @f) (getFinite round + 2)
          `append` getRoundConstants (Proxy @f) (getFinite round + 3)
          `append`
            getRoundConstants (Proxy @f) (getFinite round + 4)
    in
      addRow { kind: PoseidonGate, coeffs, variables }

foreign import verifyPallasPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Pallas.ScalarField)) Boolean

foreign import verifyVestaPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Vesta.ScalarField)) Boolean

verifyPallasPoseidon :: Vector 12 (Vector 15 Pallas.ScalarField) -> Boolean
verifyPallasPoseidon witness = runFn2 verifyPallasPoseidonGadget 12 witness

verifyVestaPoseidon :: Vector 12 (Vector 15 Vesta.ScalarField) -> Boolean
verifyVestaPoseidon witness = runFn2 verifyVestaPoseidonGadget 12 witness