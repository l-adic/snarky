module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , eval
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (and, foldl)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Type.Proxy (Proxy(..))
import Poseidon.Class (class PoseidonField, getRoundConstants, getMdsMatrix, sbox)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Snarky.Data.Fin (Finite, unsafeFinite)

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
  allStates <- traverse (evaluateState lookup) constraint.state
  let roundChecks = map (validateRoundTransition allStates) (Array.range 0 54)
  in and roundChecks

validateRoundTransition
  :: forall f
   . PoseidonField f
  => PrimeField f
  => Vector 56 (Vector 3 (F f))
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
  :: forall f
   . PoseidonField f
  => PrimeField f
  => Vector 3 f
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
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> Vector 3 (FVar f)
  -> m (Vector 3 (F f))
evaluateState lookup stateVec =
  traverse (\var -> F <$> CVar.eval lookup var) stateVec