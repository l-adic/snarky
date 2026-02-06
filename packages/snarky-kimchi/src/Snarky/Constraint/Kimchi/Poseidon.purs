module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , Rows
  , class PoseidonVerifiable
  , verifyPoseidon
  , eval
  , reduce
  ) where

import Prelude hiding (append)

import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Vector (Vector, append, head, (!!))
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField, getRoundConstants)
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

type PoseidonConstraint f =
  { state :: Vector 56 (Vector 3 (FVar f))
  }

class PoseidonField f <= PoseidonVerifiable f where
  verifyPoseidon :: Vector 12 (Vector 15 f) -> Boolean

newtype Rows f = Rows (Vector 12 (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Vector.toUnfoldable as

eval
  :: forall f m
   . PrimeField f
  => PoseidonVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup (Rows rows) =
  let
    lookup' = maybe (pure zero) lookup
  in
    verifyPoseidon <$> traverse (\r -> traverse lookup' r.variables) rows

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

foreign import verifyPallasPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Pallas.ScalarField)) Boolean

foreign import verifyVestaPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Vesta.ScalarField)) Boolean

instance PoseidonVerifiable Pallas.ScalarField where
  verifyPoseidon = runFn2 verifyPallasPoseidonGadget 12

instance PoseidonVerifiable Vesta.ScalarField where
  verifyPoseidon = runFn2 verifyVestaPoseidonGadget 12