module Snarky.Test.Circuit.Circuit (spec) where

import Prelude

import Data.Array (filter, foldMap, (..))
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.Either (Either(..))
import Data.Foldable (for_, sum)
import Data.Identity (Identity)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Effect.Aff (throwError)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilder)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, all_, and_, any_, div_, eq_, ifThenElse_, inv_, mul_, not_, or_, publicInputs, read, runAsProver, square_, sum_, xor_)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProver)
import Snarky.Circuit.Types (class ConstrainedType, BooleanVariable, FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Types (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (Result, arbitrary, quickCheckGen, withHelp)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = BN254.ScalarField

type Inputs2 =
  Tuple
    (FieldElem Fr)
    (FieldElem Fr)

mulCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr Variable)
mulCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    mul_ a b

squareCircuit
  :: forall m p
   . CircuitM Fr m p
  => m (CVar Fr Variable)
squareCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    square_ a

eqCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
eqCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    eq_ a b

invCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr Variable)
invCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    inv_ a

divCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr Variable)
divCircuit =
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    div_ a b

notCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
notCircuit = do
  publicInputs @Fr (Proxy @Boolean) >>= \a ->
    pure $ not_ a

type BoolInputs2 =
  Tuple
    Boolean
    Boolean

andCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
andCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    and_ a b

orCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
orCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    or_ a b

xorCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
xorCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    xor_ a b

type IfThenElseInputs =
  Tuple3 Boolean (FieldElem Fr) (FieldElem Fr)

ifThenElseCircuit
  :: forall m n
   . CircuitM Fr m n
  => m (CVar Fr Variable)
ifThenElseCircuit =
  publicInputs @Fr (Proxy @IfThenElseInputs) >>= \(Tuple b (Tuple t e)) ->
    ifThenElse_ b t e

intSizes :: NonEmptyArray Int
intSizes = case fromArray $ filter (\x -> x `mod` 8 == 0) (8 .. 256) of
  Nothing -> unsafeCrashWith "intSizes: impossible"
  Just x -> x

allCircuit
  :: forall m n p
   . CircuitM Fr m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr BooleanVariable)
allCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    all_ (unVector bs)

anyCircuit
  :: forall m n p
   . CircuitM Fr m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr BooleanVariable)
anyCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    any_ (unVector bs)

sumCircuit
  :: forall m n p
   . CircuitM Fr m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr Variable)
sumCircuit _ =
  publicInputs @Fr (Proxy @(Vector n (FieldElem Fr))) >>= \bs ->
    pure $ sum_ (unVector bs)

mkCircuitSpec
  :: forall f a b avar bvar
   . PrimeField f
  => ConstrainedType f avar a
  => ConstrainedType f bvar b
  => Eq b
  => Proxy f
  -> Gen a
  -> (forall m. CircuitM f m Identity => m bvar)
  -> (a -> b)
  -> Gen Result
mkCircuitSpec (_ :: Proxy f) inputsGen circuit f = do
  inputs <- inputsGen
  let
    Tuple _ { constraints, publicInputs } =
      runCircuitBuilder circuit (emptyCircuitBuilderState :: CircuitBuilderState f)
    Tuple result (assignments :: Map Variable f) =
      let
        proverState = emptyProverState { publicInputs = publicInputs }
      in
        case runProver (assignPublicInputs inputs *> circuit) proverState of
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
  pure $
    case eres of
      Right res -> withHelp res "Circuit constraints satisfied and evals correctly"
      Left e -> withHelp false ("Failed to parse circuit output: " <> show e)

spec :: Spec Unit
spec = describe "Circuit Specs" do

  it "mul Circuit is Valid" $ quickCheck $
    mkCircuitSpec (Proxy @Fr) arbitrary mulCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      FieldElem @Fr (a * b)

  it "square Circuit is Valid" $ quickCheck $
    mkCircuitSpec (Proxy @Fr) arbitrary squareCircuit \(FieldElem a) ->
      FieldElem @Fr (a * a)

  it "eq Circuit is Valid" $ quickCheck $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f = uncurry (==)
    in
      mkCircuitSpec (Proxy @Fr) arbitrary eqCircuit f

  it "inv Circuit is Valid" $ quickCheck $
    mkCircuitSpec (Proxy @Fr) arbitrary invCircuit \(FieldElem a) ->
      if a == zero then FieldElem zero
      else FieldElem @Fr (recip a)

  it "div Circuit is Valid" $ quickCheck $
    mkCircuitSpec (Proxy @Fr) arbitrary divCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      if b == zero then FieldElem zero
      else FieldElem @Fr (a / b)

  it "not Circuit is Valid" $ quickCheck $
    let
      f :: Boolean -> Boolean
      f = not
    in
      mkCircuitSpec (Proxy @Fr) arbitrary notCircuit f

  it "and Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
    in
      mkCircuitSpec (Proxy @Fr) arbitrary andCircuit f

  it "or Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
    in
      mkCircuitSpec (Proxy @Fr) arbitrary orCircuit f

  it "xor Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
    in
      mkCircuitSpec (Proxy @Fr) arbitrary xorCircuit f

  it "ifThenElse Circuit is Valid" $ quickCheck $
    let
      f :: Tuple3 Boolean (FieldElem Fr) (FieldElem Fr) -> FieldElem Fr
      f = uncurry3 \b t e ->
        if b then t else e
    in
      mkCircuitSpec (Proxy @Fr) arbitrary ifThenElseCircuit f

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Proxy @Fr) (Vector.generator pk arbitrary) (allCircuit pk) f

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Proxy @Fr) (Vector.generator pk arbitrary) (anyCircuit pk) f

  it "sum Circuit is Valid" $
    let
      f :: forall n. Vector n (FieldElem Fr) -> FieldElem Fr
      f as = FieldElem $ sum (un FieldElem <$> as)
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Proxy @Fr) (Vector.generator pk arbitrary) (sumCircuit pk) f