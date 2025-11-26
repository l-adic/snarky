module Snarky.Test.Circuit.CVar (spec) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExcept)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (foldl, maximum, traverse)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, eval, evalAffineExpression, incrementVariable, reduceToAffineExpression, v0)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint (R1CS(..), evalR1CSConstraint)
import Snarky.Circuit.Plonk as Plonk
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary, quickCheckGen, quickCheckGen', (===))
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Collect all variable identifiers used in an AffineCircuit
genCVarWithAssignments
  :: forall f
   . PrimeField f
  => Gen
       { cvar :: CVar f Variable
       , assignments :: Map Variable f
       }
genCVarWithAssignments = do
  cvar <- arbitrary @(CVar f Variable)
  assignments <- genAssignments $ collectVariables cvar
  pure
    { cvar
    , assignments
    }
  where
  collectVariables = foldl (flip Set.insert) Set.empty
  genAssignments vars = do
    let varArray = Set.toUnfoldable vars :: Array Variable
    assignments <- traverse (\_ -> arbitrary @f) varArray
    pure $ Map.fromFoldable $ Array.zip varArray assignments

genR1CSWithAssignments
  :: forall f
   . PrimeField f
  => Show f
  => Proxy f
  -> Gen
       { r1cs :: R1CS f
       , assignments :: Map Variable f
       }
genR1CSWithAssignments _ = do
  { cvar: left, assignments: a1 } <- genCVarWithAssignments
  { cvar: right, assignments: a2 } <- genCVarWithAssignments
  { cvar: output, assignments: a3 } <- genCVarWithAssignments
  let
    assignments = Map.unions [ a1, a2, a3 ]
    lookup v = case Map.lookup v assignments of
      Nothing -> throwError $ MissingVariable v
      Just a -> pure a
    eres = runExcept do
      l <- CVar.eval lookup left
      r <- CVar.eval lookup right
      o <- CVar.eval lookup output
      pure
        if o == zero then ScalarMul zero output
        else ScalarMul (l * r / o) output
  case eres of
    Left (e :: EvaluationError f) -> unsafeCrashWith $ "Unexpected error when generating r1cs: " <> show e
    Right output' ->
      pure
        { r1cs: R1CS { left, right, output: output' }
        , assignments
        }

spec :: Spec Unit
spec = describe "Constraint Spec" do

  it "CVar.eval equals evalAffineExpression after reduction" do
    liftEffect $ quickCheckGen do
      { cvar, assignments } <- genCVarWithAssignments
      let
        _lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
      let
        lhs :: Either (EvaluationError BN254.ScalarField) BN254.ScalarField
        lhs = runExcept $ evalAffineExpression (reduceToAffineExpression cvar) _lookup
      let rhs = runExcept $ eval _lookup cvar
      pure $ lhs == rhs

  it "r1cs gen is valid" do
    liftEffect $ quickCheckGen do
      { r1cs, assignments } <- genR1CSWithAssignments (Proxy @BN254.ScalarField)
      let
        lookup v = case Map.lookup v assignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        res :: Either (EvaluationError (BN254.ScalarField)) Boolean
        res = runExcept $ evalR1CSConstraint lookup r1cs
      pure $ res == Right true

  it "reduces r1cs constraints to plonk constraints" do
    liftEffect $ quickCheckGen' 10000 do
      { r1cs, assignments } <- genR1CSWithAssignments (Proxy @BN254.ScalarField)
      let
        nextVariable = maybe v0 incrementVariable $ maximum (Map.keys assignments)
        plonkConstraints = Plonk.reduceAsBuilder { nextVariable, constraints: [ r1cs ] }
        finalAssignments = case Plonk.reduceAsProver [ r1cs ] { nextVariable, assignments } of
          Left e -> unsafeCrashWith $ "Unexpected error in Plonk reduce as Prover: " <> show e
          Right { assignments: assignments' } -> assignments'
        lookup v = case Map.lookup v finalAssignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        r1csEval :: Either (EvaluationError (BN254.ScalarField)) Boolean
        r1csEval = runExcept $ evalR1CSConstraint lookup r1cs
        plonkEval = runExcept $
          foldM
            ( \acc c ->
                Plonk.evalPlonkConstraint lookup c <#> conj acc
            )
            true
            plonkConstraints.constraints
      pure $ plonkEval === r1csEval
