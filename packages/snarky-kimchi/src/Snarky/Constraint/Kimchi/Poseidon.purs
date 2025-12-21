module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , eval
  , reducePoseidon
  ) where

import Prelude hiding (append)

import Data.Array as Array
import Data.Foldable (and, foldl)
import Data.FoldableWithIndex (traverseWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Poseidon.Class (class PoseidonField, getMdsMatrix, getRoundConstants, sbox)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (Finite, getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector, append, head, (!!))
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))

type PoseidonConstraint f =
  { state :: Vector 56 (Vector 3 (FVar f))
  }

eval
  :: forall f m
   . PoseidonField f
  => PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> PoseidonConstraint f
  -> m Boolean
eval lookup constraint = ado
  allStates <- traverse evaluateState constraint.state
  let roundChecks = map (validateRoundTransition allStates) (Array.range 0 54)
  in and roundChecks
  where
  validateRoundTransition
    :: Vector 56 (Vector 3 (F f))
    -> Int
    -> Boolean
  validateRoundTransition allStates round =
    let
      inputState = Vector.index allStates (unsafeFinite round)
      outputState = Vector.index allStates (unsafeFinite (round + 1))
      sboxInputs = map (\(F x) -> sbox x) inputState
      roundConstants = getRoundConstants (Proxy :: Proxy f) round
      expected = computeRoundOutput sboxInputs roundConstants
    in
      map (\(F x) -> x) outputState == map (\(F x) -> x) expected

  computeRoundOutput
    :: Vector 3 f
    -> Vector 3 f
    -> Vector 3 (F f)
  computeRoundOutput sboxInputs roundConstants =
    let
      mdsMatrix = getMdsMatrix (Proxy :: Proxy f)

      computeElement :: Finite 3 -> F f
      computeElement j =
        let
          roundConstant = Vector.index roundConstants j
          mdsRow = Vector.index mdsMatrix j
          mdsSum = foldl (\acc (Tuple mdsCoeff sboxInput) -> acc + mdsCoeff * sboxInput) zero
            (Vector.zip mdsRow sboxInputs)
          expectedOutput = roundConstant + mdsSum
        in
          F expectedOutput
    in
      Vector.generate computeElement

  evaluateState
    :: Vector 3 (FVar f)
    -> m (Vector 3 (F f))
  evaluateState stateVec =
    traverse (\var -> F <$> CVar.eval lookup var) stateVec

reducePoseidon
  :: forall f m
   . PrimeField f
  => PoseidonField f
  => PlonkReductionM m f
  => PoseidonConstraint f
  -> m Unit
reducePoseidon c = do
  state <- traverse (traverse reduceToVariable) c.state
  -- after :: Vector 1 (Vector 3) Variable
  let { before, after } = Vector.splitAt (Proxy @55) state
  let rounds = Vector.chunks (Proxy @5) before
  traverseWithIndex_ addRoundState rounds
  let lastRowVars = map Just (head after) `append` Vector.generate (const Nothing)
  addRow lastRowVars { kind: Zero, coeffs: Vector.generate (const zero) }
  where
  addRoundState :: Finite 11 -> Vector 5 (Vector 3 Variable) -> m Unit
  addRoundState round s =
    let
      vars = map Just $
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
      addRow vars { kind: PoseidonGate, coeffs }