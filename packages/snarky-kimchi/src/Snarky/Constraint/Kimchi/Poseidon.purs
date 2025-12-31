module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , eval
  , reduce
  , class PoseidonVerifiable
  , verifyPoseidon
  ) where

import Prelude hiding (append)

import Data.Function.Uncurried (Fn2, runFn2)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, getRoundConstants)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (Finite, getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector, append, head, (!!))
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
  -> Vector 12 (KimchiRow f)
  -> m Boolean
eval lookup rows =
  let
    lookup' = maybe (pure zero) lookup
  in
    verifyPoseidon <$> traverse (\r -> traverse lookup' r.variables) rows

reduce
  :: forall f m
   . PrimeField f
  => PoseidonField f
  => PlonkReductionM m f
  => PoseidonConstraint f
  -> m (Vector 12 (KimchiRow f))
reduce c = do
  state <- traverse (traverse reduceToVariable) c.state
  let
    { before, after } = Vector.splitAt @55 state
    rounds = mapWithIndex addRoundState $ Vector.chunks @5 before
    lastRowVars = map Just (head after) `append` Vector.generate (const Nothing)
  pure $ rounds `Vector.snoc` { kind: Zero, coeffs: Vector.generate (const zero), variables: lastRowVars }
  where
  addRoundState :: Finite 11 -> Vector 5 (Vector 3 Variable) -> KimchiRow f
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
      { kind: PoseidonGate, coeffs, variables }

foreign import verifyPallasPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Pallas.ScalarField)) Boolean

foreign import verifyVestaPoseidonGadget
  :: Fn2 Int (Vector 12 (Vector 15 Vesta.ScalarField)) Boolean

verifyPallasPoseidon :: Vector 12 (Vector 15 Pallas.ScalarField) -> Boolean
verifyPallasPoseidon witness = runFn2 verifyPallasPoseidonGadget 12 witness

verifyVestaPoseidon :: Vector 12 (Vector 15 Vesta.ScalarField) -> Boolean
verifyVestaPoseidon witness = runFn2 verifyVestaPoseidonGadget 12 witness