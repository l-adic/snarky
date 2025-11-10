module Snarky.Test.Circuit.Circuit where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Effect.Aff (Aff, throwError)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilderM)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, all_, and_, div_, eq_, ifThenElse_, inv_, mul_, not_, publicInputs, read, runAsProver, square_, xor_)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProverM)
import Snarky.Circuit.Types (class ConstrainedType, BooleanVariable(..), FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Types (class PrimeField)
import Test.QuickCheck (class Arbitrary, withHelp)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = BN254.ScalarField

type Inputs2 =
  Tuple
    (FieldElem Fr)
    (FieldElem Fr)

mulCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr Variable)
mulCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    mul_ a b

squareCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr Variable)
squareCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    square_ a

eqCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr BooleanVariable)
eqCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    eq_ a b

invCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr Variable)
invCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    inv_ a

divCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr Variable)
divCircuit =
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    div_ a b

notCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr BooleanVariable)
notCircuit = do
  publicInputs @Fr (Proxy @Boolean) >>= \a ->
    pure $ not_ a

type BoolInputs2 =
  Tuple
    Boolean
    Boolean

andCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr BooleanVariable)
andCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    and_ a b

xorCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr BooleanVariable)
xorCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    xor_ a b

type IfThenElseInputs =
  Tuple3 Boolean (FieldElem Fr) (FieldElem Fr)

ifThenElseCircuit
  :: forall m
   . CircuitM Fr m
  => m (CVar Fr Variable)
ifThenElseCircuit =
  publicInputs @Fr (Proxy @IfThenElseInputs) >>= \(Tuple b (Tuple t e)) ->
    ifThenElse_ b t e

{-
allCircuit
  :: forall m
  . CircuitM Fr m
  => m (CVar Fr BooleanVariable)
allCircuit =
  publicInputs @Fr (Proxy @(Array Boolean)) >>= \bs ->
    all_ bs
-}

mkCircuitSpec
  :: forall f a b avar bvar
   . PrimeField f
  => ConstrainedType f avar a
  => ConstrainedType f bvar b
  => Arbitrary a
  => Eq b
  => Proxy f
  -> (forall m. CircuitM f m => m bvar)
  -> (a -> b)
  -> Aff Unit
mkCircuitSpec (_ :: Proxy f) circuit f = quickCheck $ \inputs ->
  let
    Tuple _ { constraints, publicInputs } =
      runCircuitBuilderM circuit (emptyCircuitBuilderState :: CircuitBuilderState f)
    Tuple result assignments =
      let
        proverState = emptyProverState { publicInputs = publicInputs }
      in
        case runProverM (assignPublicInputs inputs *> circuit) proverState of
          Tuple (Left e) _ -> unsafeCrashWith $ "Error in circuit: " <> show e
          Tuple (Right c) { assignments } -> Tuple c assignments
    _lookup v = case Map.lookup v assignments of
      Nothing -> throwError $ MissingVariable v
      Just res -> pure res
    eres = runAsProver
      ( do
          isSatisfied <- evalR1CSCircuit _lookup (R1CSCircuit constraints)
          b <- read result
          pure $ isSatisfied && f inputs == b
      )
      assignments
  in
    case eres of
      Right res -> withHelp res "Circuit constraints satisfied and evals correctly"
      Left e -> withHelp false ("Failed to parse circuit output: " <> show e)

spec :: Spec Unit
spec = describe "Circuit Specs" do

  it "mul Circuit is Valid" $
    mkCircuitSpec (Proxy @Fr) mulCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      FieldElem @Fr (a * b)

  it "square Circuit is Valid" $
    mkCircuitSpec (Proxy @Fr) squareCircuit \(FieldElem a) ->
      FieldElem @Fr (a * a)

  it "eq Circuit is Valid" $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f = uncurry (==)
    in
      mkCircuitSpec (Proxy @Fr) eqCircuit f

  it "inv Circuit is Valid" $
    mkCircuitSpec (Proxy @Fr) invCircuit \(FieldElem a) ->
      if a == zero then FieldElem zero
      else FieldElem @Fr (recip a)

  it "div Circuit is Valid" $
    mkCircuitSpec (Proxy @Fr) divCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      if b == zero then FieldElem zero
      else FieldElem @Fr (a / b)

  it "not Circuit is Valid" $
    let
      f :: Boolean -> Boolean
      f = not
    in
      mkCircuitSpec (Proxy @Fr) notCircuit f

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
    in
      mkCircuitSpec (Proxy @Fr) andCircuit f

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
    in
      mkCircuitSpec (Proxy @Fr) xorCircuit f

  it "ifThenElse Circuit is Valid" $
    let
      f :: Tuple3 Boolean (FieldElem Fr) (FieldElem Fr) -> FieldElem Fr
      f = uncurry3 \b t e ->
        if b then t else e
    in
      mkCircuitSpec (Proxy @Fr) ifThenElseCircuit f