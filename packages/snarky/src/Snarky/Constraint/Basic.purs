-- | Basic constraint types for zero-knowledge circuits.
-- |
-- | This module provides the fundamental constraint types used in circuit
-- | construction. These constraints form the building blocks that backends
-- | compile into their native formats (R1CS, Plonk gates, etc.).
-- |
-- | ## Constraint Types
-- |
-- | - **R1CS**: Rank-1 Constraint System - `left × right = output`
-- | - **Equal**: Equality constraint between two expressions
-- | - **Boolean**: Range constraint ensuring a value is 0 or 1
-- |
-- | ```purescript
-- | import Snarky.Constraint.Basic (r1cs, equal, boolean)
-- |
-- | -- Multiplication constraint: a × b = c
-- | mulConstraint = r1cs { left: a, right: b, output: c }
-- |
-- | -- Equality constraint: x = y
-- | eqConstraint = equal x y
-- |
-- | -- Boolean constraint: b ∈ {0, 1}
-- | boolConstraint = boolean b
-- | ```
-- |
-- | ## The BasicSystem Type Class
-- |
-- | The `BasicSystem` class abstracts over concrete constraint representations,
-- | allowing backends to define their own constraint types while sharing
-- | circuit construction logic.
module Snarky.Constraint.Basic
  ( Basic(..)
  , eval
  , debugCheck
  , genWithAssignments
  , class BasicSystem
  , fromBasic
  , r1cs
  , boolean
  , equal
  , square
  ) where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, runExcept)
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.CVar (CVar, EvaluationError(..), Variable, add_, scale_, v0)
import Snarky.Circuit.CVar as CVar
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, frequency)
import Type.Proxy (Proxy)

-- | The basic constraint type parameterized by field `f`.
-- |
-- | These are the fundamental constraints supported by most ZK backends.
data Basic f
  = R1CS
      { left :: CVar f Variable
      , right :: CVar f Variable
      , output :: CVar f Variable
      }
  -- ^ Rank-1 constraint: `left × right = output`
  | Equal (CVar f Variable) (CVar f Variable)
  -- ^ Equality constraint: the two expressions must be equal
  | Square (CVar f Variable) (CVar f Variable)
  -- ^ Square constraint: `a × a = c`
  | Boolean (CVar f Variable)

-- ^ Boolean constraint: the expression must evaluate to 0 or 1

derive instance Functor Basic
derive instance Generic (Basic f) _

-- | Evaluate a constraint given variable assignments.
-- |
-- | Returns `true` if the constraint is satisfied, `false` otherwise.
-- | The lookup function provides values for circuit variables.
eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> Basic f
  -> m Boolean
eval lookup gate =
  case gate of
    R1CS { left, right, output } -> ado
      lval <- CVar.eval lookup left
      rval <- CVar.eval lookup right
      oval <- CVar.eval lookup output
      in lval * rval == oval
    Equal a b ->
      lift2 eq (CVar.eval lookup a) (CVar.eval lookup b)
    Square a c -> ado
      aval <- CVar.eval lookup a
      cval <- CVar.eval lookup c
      in aval * aval == cval
    Boolean i -> do
      CVar.eval lookup i <#> \inp ->
        inp == zero || inp == one

-- | Eagerly check a Basic constraint against current variable assignments.
-- | Returns `Nothing` if satisfied, `Just errorMessage` if violated.
debugCheck
  :: forall f
   . PrimeField f
  => (Variable -> Maybe f)
  -> Basic f
  -> Maybe EvaluationError
debugCheck lookupVar c =
  let
    lookup :: Variable -> Except EvaluationError f
    lookup v = case lookupVar v of
      Nothing -> throwError $ MissingVariable v
      Just val -> pure val

    evalCVar :: CVar f Variable -> String
    evalCVar cv = case runExcept (CVar.eval lookup cv) of
      Left _ -> "[unknown]"
      Right val -> show val
  in
    case runExcept (eval lookup c) of
      Left e -> Just e
      Right satisfied
        | satisfied -> Nothing
        | otherwise -> Just $ FailedAssertion $ case c of
            R1CS { left, right, output } ->
              "R1CS failed: " <> evalCVar left <> " * " <> evalCVar right <> " != " <> evalCVar output
            Equal a b ->
              "Equal failed: " <> evalCVar a <> " != " <> evalCVar b
            Square a sq ->
              "Square failed: " <> evalCVar a <> "^2 != " <> evalCVar sq
            Boolean v ->
              "Boolean failed: " <> evalCVar v <> " not in {0,1}"

-- | Generate a random constraint with satisfying variable assignments.
-- |
-- | Used for property-based testing of constraint evaluation and backends.
genWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { basic :: Basic f
       , assignments :: Map Variable f
       }
genWithAssignments pf =
  let
    genBool = do
      { cvar, assignments } <- CVar.genWithAssignments pf v0
      let
        lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
        eres = runExcept $ CVar.eval lookup cvar

        b :: f
        b = case eres of
          Left (e :: EvaluationError) ->
            unsafeThrow $ "Unexpected error when generating boolean cvar" <> show e
          Right a -> a
      cvar' <-
        if b == zero || b == one then pure cvar
        else do
          b' <- arbitrary
          pure
            if b' then (scale_ (recip b) cvar)
            else add_ cvar (scale_ (-one) cvar)
      pure { basic: Boolean cvar', assignments }

    genEqual = do
      { cvar: left, assignments: a1, nextVariable } <- CVar.genWithAssignments pf v0
      { cvar: right, assignments: a2 } <- CVar.genWithAssignments pf nextVariable
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
            else if l == zero then (scale_ zero right)
            else (scale_ (l / r) right)
      case eres of
        Left (e :: EvaluationError) -> unsafeThrow $ "Unexpected error when generating r1cs: " <> show e
        Right right' ->
          pure
            { basic: Equal left right'
            , assignments
            }

    genR1CS = do
      { cvar: left, assignments: a1, nextVariable: v1 } <- CVar.genWithAssignments pf v0
      { cvar: right, assignments: a2, nextVariable: v2 } <- CVar.genWithAssignments pf v1
      { cvar: output, assignments: a3 } <- CVar.genWithAssignments pf v2
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
            if o == zero then scale_ zero output
            else scale_ (l * r / o) output
      case eres of
        Left (e :: EvaluationError) ->
          unsafeThrow $ "Unexpected error when generating r1cs: " <> (show @EvaluationError e)
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

-- | Type class for constraint systems supporting basic constraint types.
-- |
-- | This abstracts over concrete constraint representations, allowing
-- | different backends to provide their own implementations while sharing
-- | the circuit DSL.
-- |
-- | The functional dependency `c -> f` ensures each constraint type
-- | determines its field type.
class PrimeField f <= BasicSystem f c | c -> f where
  -- | Create an R1CS constraint: `left × right = output`
  r1cs :: { left :: CVar f Variable, right :: CVar f Variable, output :: CVar f Variable } -> c
  -- | Create an equality constraint: the two expressions must be equal
  equal :: CVar f Variable -> CVar f Variable -> c
  -- | Create a square constraint: `a × a = c`
  square :: CVar f Variable -> CVar f Variable -> c
  -- | Create a boolean constraint: the expression must be 0 or 1
  boolean :: CVar f Variable -> c

-- | Convert a `Basic` constraint to any `BasicSystem` constraint type.
-- |
-- | This allows using the concrete `Basic` type as an intermediate
-- | representation before converting to backend-specific formats.
fromBasic :: forall f c. BasicSystem f c => Basic f -> c
fromBasic = case _ of
  R1CS r -> r1cs r
  Equal a b -> equal a b
  Square a c -> square a c
  Boolean b -> boolean b

instance PrimeField f => BasicSystem f (Basic f) where
  r1cs = R1CS
  equal = Equal
  square = Square
  boolean = Boolean
