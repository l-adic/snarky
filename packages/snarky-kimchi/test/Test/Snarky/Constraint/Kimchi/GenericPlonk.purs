module Test.Snarky.Constraint.Kimchi.GenericPlonk (spec) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (ExceptT, except, runExcept, runExceptT, throwError)
import Control.Monad.State (class MonadState, State, execState, get, modify_, runState)
import Data.Array as A
import Data.Either (Either(..))
import Data.Foldable (foldM, traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un)
import Data.Traversable (maximum)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (EvaluationError(..), Variable, evalAffineExpression, incrementVariable, v0)
import Snarky.Constraint.Basic (Basic)
import Snarky.Constraint.Basic as Basic
import Snarky.Constraint.Kimchi.GenericPlonk (class PlonkReductionM, GenericPlonkConstraint, reduceBasic)
import Snarky.Constraint.Kimchi.GenericPlonk as Plonk
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (quickCheckGen', (===))
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "Constraint Spec" do

  it "reduces basic constraints to plonk constraints" do
    liftEffect $ quickCheckGen' 10000 do
      { basic, assignments } <- Basic.genWithAssignments pf
      let
        nextVariable = maybe v0 incrementVariable $ maximum (Map.keys assignments)
        plonkConstraints = reduceAsBuilder { nextVariable, constraints: [ basic ] }
        finalAssignments = case reduceAsProver [ basic ] { nextVariable, assignments } of
          Left e -> unsafeCrashWith $ "Unexpected error in Plonk reduce as Prover: " <> show e
          Right { assignments: assignments' } -> assignments'
        lookup v = case Map.lookup v finalAssignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        basicEval :: Either (EvaluationError f) Boolean
        basicEval = runExcept $ Basic.eval lookup basic
        plonkEval = runExcept $
          foldM
            ( \acc c ->
                Plonk.eval lookup c <#> conj acc
            )
            true
            plonkConstraints.constraints
      pure $ plonkEval === basicEval


reduceAsBuilder
  :: forall f
   . PrimeField f
  => { nextVariable :: Variable
     , constraints :: Array (Basic f)
     }
  -> { nextVariable :: Variable
     , constraints :: Array (GenericPlonkConstraint f)
     }
reduceAsBuilder { nextVariable, constraints: cs } =
  let
    initState = BuilderReductionState { nextVariable, constraints: mempty }
    BuilderReductionState s = execState (un PlonkBuilder (traverse_ reduceBasic cs)) initState
  in
    s

reduceAsProver
  :: forall f
   . PrimeField f
  => Array (Basic f)
  -> { nextVariable :: Variable
     , assignments :: Map Variable f
     }
  -> Either
       (EvaluationError f)
       { nextVariable :: Variable
       , assignments :: Map Variable f
       }
reduceAsProver cs s = case runState (runExceptT $ un PlonkProver (traverse_ (reduceBasic) cs)) (ProverReductionState s) of
  Tuple (Left e) _ -> Left e
  Tuple (Right _) (ProverReductionState s') -> Right s'


newtype BuilderReductionState f = BuilderReductionState
  { constraints :: Array (GenericPlonkConstraint f)
  , nextVariable :: Variable
  }

newtype PlonkBuilder f a = PlonkBuilder (State (BuilderReductionState f) a)

derive newtype instance Functor (PlonkBuilder f)
derive newtype instance Apply (PlonkBuilder f)
derive newtype instance Applicative (PlonkBuilder f)
derive newtype instance Bind (PlonkBuilder f)
derive newtype instance Monad (PlonkBuilder f)
derive newtype instance MonadState (BuilderReductionState f) (PlonkBuilder f)

derive instance Newtype (PlonkBuilder f a) _

instance PlonkReductionM (PlonkBuilder f) f where
  addGenericPlonkConstraint c =
    modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { constraints = s.constraints `A.snoc` c }
  createInternalVariable _ = do
    BuilderReductionState { nextVariable } <- get
    modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { nextVariable = incrementVariable nextVariable }
    pure nextVariable

newtype ProverReductionState f = ProverReductionState
  { nextVariable :: Variable
  , assignments :: Map Variable f
  }

newtype PlonkProver f a = PlonkProver (ExceptT (EvaluationError f) (State (ProverReductionState f)) a)

derive newtype instance Functor (PlonkProver f)
derive newtype instance Apply (PlonkProver f)
derive newtype instance Applicative (PlonkProver f)
derive newtype instance Bind (PlonkProver f)
derive newtype instance Monad (PlonkProver f)
derive newtype instance MonadState (ProverReductionState f) (PlonkProver f)
derive newtype instance MonadThrow (EvaluationError f) (PlonkProver f)

derive instance Newtype (PlonkProver f a) _

instance (PrimeField f) => PlonkReductionM (PlonkProver f) f where
  addGenericPlonkConstraint _ = pure unit
  createInternalVariable e = do
    ProverReductionState { nextVariable, assignments } <- get
    let
      _lookup v = case Map.lookup v assignments of
        Nothing ->
          throwError $ MissingVariable v
        Just a -> pure a
    a <- evalAffineExpression e _lookup
    modify_ \(ProverReductionState s) -> ProverReductionState $
      s
        { nextVariable = incrementVariable nextVariable
        , assignments = Map.insert nextVariable a assignments

        }
    pure nextVariable