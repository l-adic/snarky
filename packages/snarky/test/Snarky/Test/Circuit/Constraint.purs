module Snarky.Test.Circuit.Constraint (spec) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExcept)
import Control.Monad.Gen (frequency)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (foldl, maximum, traverse)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, eval, evalAffineExpression, incrementVariable, reduceToAffineExpression, v0)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint (Basic(..), evalBasicConstraint)
import Snarky.Circuit.Plonk as Plonk
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary, quickCheckGen, quickCheckGen', (===))
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

-- | Collect all variable identifiers used in an AffineCircuit
genCVarWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { cvar :: CVar f Variable
       , assignments :: Map Variable f
       }
genCVarWithAssignments _ = do
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

genBasicWithAssignments
  :: forall f
   . PrimeField f
  => Show f
  => Proxy f
  -> Gen
       { basic :: Basic f
       , assignments :: Map Variable f
       }
genBasicWithAssignments pf =
  let
    genBool = do
      { cvar, assignments } <- genCVarWithAssignments pf
      let
        lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
        eres = runExcept $ CVar.eval lookup cvar

        b :: f
        b = case eres of
          Left (e :: EvaluationError f) -> unsafeCrashWith $ "Unexpected error when generating boolean cvar" <> show e
          Right a -> a
      cvar' <-
        if b == zero || b == one then pure cvar
        else do
          b' <- arbitrary
          pure
            if b' then (ScalarMul (recip b) cvar)
            else Add cvar (ScalarMul (-one) cvar)
      pure { basic: Boolean cvar', assignments }

    genEqual = do
      { cvar: left, assignments: a1 } <- genCVarWithAssignments pf
      { cvar: right, assignments: a2 } <- genCVarWithAssignments pf
      let
        assignments = Map.unions [ a1, a2 ]
        lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
        eres = runExcept do
          l <- CVar.eval lookup left
          r <- CVar.eval lookup right
          pure
            if l == r then right
            else if l == zero then (ScalarMul zero right)
            else (ScalarMul (l / r) right)
      case eres of
        Left (e :: EvaluationError f) -> unsafeCrashWith $ "Unexpected error when generating r1cs: " <> show e
        Right right' ->
          pure
            { basic: Equal left right'
            , assignments
            }

    genR1CS = do
      { cvar: left, assignments: a1 } <- genCVarWithAssignments pf
      { cvar: right, assignments: a2 } <- genCVarWithAssignments pf
      { cvar: output, assignments: a3 } <- genCVarWithAssignments pf
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
            { basic: R1CS { left, right, output: output' }
            , assignments
            }
  in
    frequency $ NEA.cons'
      ( Tuple 10.0 genR1CS
      )
      [ Tuple 1.0 genBool
      , Tuple 4.0 genEqual
      ]

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "Constraint Spec" do

  it "CVar.eval equals evalAffineExpression after reduction" do
    liftEffect $ quickCheckGen do
      { cvar, assignments } <- genCVarWithAssignments pf
      let
        _lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
      let
        lhs :: Either (EvaluationError f) f
        lhs = runExcept $ evalAffineExpression (reduceToAffineExpression cvar) _lookup
      let rhs = runExcept $ eval _lookup cvar
      pure $ lhs == rhs

  it "basic constraint gen is valid" do
    liftEffect $ quickCheckGen do
      { basic, assignments } <- genBasicWithAssignments pf
      let
        lookup v = case Map.lookup v assignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        res :: Either (EvaluationError (BN254.ScalarField)) Boolean
        res = runExcept $ evalBasicConstraint lookup basic
      pure $ res == Right true

  it "reduces basic constraints to plonk constraints" do
    liftEffect $ quickCheckGen' 10000 do
      { basic, assignments } <- genBasicWithAssignments pf
      let
        nextVariable = maybe v0 incrementVariable $ maximum (Map.keys assignments)
        plonkConstraints = Plonk.reduceAsBuilder { nextVariable, constraints: [ basic ] }
        finalAssignments = case Plonk.reduceAsProver [ basic ] { nextVariable, assignments } of
          Left e -> unsafeCrashWith $ "Unexpected error in Plonk reduce as Prover: " <> show e
          Right { assignments: assignments' } -> assignments'
        lookup v = case Map.lookup v finalAssignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        basicEval :: Either (EvaluationError (BN254.ScalarField)) Boolean
        basicEval = runExcept $ evalBasicConstraint lookup basic
        plonkEval = runExcept $
          foldM
            ( \acc c ->
                Plonk.evalPlonkConstraint lookup c <#> conj acc
            )
            true
            plonkConstraints.constraints
      pure $ plonkEval === basicEval
