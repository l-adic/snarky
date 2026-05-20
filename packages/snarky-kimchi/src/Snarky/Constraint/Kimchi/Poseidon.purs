module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , Rows
  , reduce
  ) where

import Prelude hiding (append)

import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Vector (Vector, append, head, (!!))
import Data.Vector as Vector
import Poseidon (class PoseidonField, getRoundConstants)
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)
import Type.Proxy (Proxy(..))

type PoseidonConstraint f =
  { state :: Vector 56 (Vector 3 (FVar f))
  }

newtype Rows f = Rows (Vector 12 (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Vector.toUnfoldable as

reduce
  :: forall f m
   . PoseidonField f
  => PlonkReductionM m f
  => PoseidonConstraint f
  -> m (Rows f)
reduce c = Rows <$> do
  state <- traverse (traverse reduceToVariable) c.state
  let
    { before, after } = Vector.splitAt @55 state
    rounds = mapWithIndex addRoundState $ Vector.chunks @5 before
    lastRowVars = map Just (head after) `append` Vector.generate (const Nothing)
  pure $ rounds `Vector.snoc` { kind: Zero, coeffs: mempty, variables: lastRowVars }
  where
  addRoundState :: Finite 11 -> Vector 5 (Vector 3 Variable) -> KimchiRow f
  addRoundState round s =
    let
      finite5 = unsafeFinite @5
      variables = map Just $
        (s !! finite5 0)
          `append` (s !! finite5 4)
          `append` (s !! finite5 1)
          `append` (s !! finite5 2)
          `append` (s !! finite5 3)
      coeffs =
        let
          baseRound = getFinite round * 5
        in
          getRoundConstants (Proxy @f) baseRound
            `append` getRoundConstants (Proxy @f) (baseRound + 1)
            `append` getRoundConstants (Proxy @f) (baseRound + 2)
            `append` getRoundConstants (Proxy @f) (baseRound + 3)
            `append`
              getRoundConstants (Proxy @f) (baseRound + 4)
    in
      { kind: PoseidonGate, coeffs: Vector.toUnfoldable coeffs, variables }

