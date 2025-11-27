module Snarky.Circuit.Constraint.Basic
  ( Basic(..)
  , eval
  , genWithAssignments
  ) where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (runExcept)
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (CVar, EvaluationError(..), Variable, add_, scale_)
import Snarky.Circuit.CVar as CVar
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, frequency)
import Type.Proxy (Proxy)

data Basic f
  = R1CS
      { left :: CVar f Variable
      , right :: CVar f Variable
      , output :: CVar f Variable
      }
  | Equal (CVar f Variable) (CVar f Variable)
  | Boolean (CVar f Variable)

derive instance Functor Basic
derive instance Generic (Basic f) _

eval
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> Basic f
  -> m Boolean
eval lookup gate = do
  case gate of
    R1CS { left, right, output } -> do
      lval <- CVar.eval lookup left
      rval <- CVar.eval lookup right
      oval <- CVar.eval lookup output
      pure $ lval * rval == oval
    Equal a b ->
      lift2 eq (CVar.eval lookup a) (CVar.eval lookup b)
    Boolean i -> do
      CVar.eval lookup i <#> \inp ->
        inp == zero || inp == one

genWithAssignments
  :: forall f
   . PrimeField f
  => Show f
  => Proxy f
  -> Gen
       { basic :: Basic f
       , assignments :: Map Variable f
       }
genWithAssignments pf =
  let
    genBool = do
      { cvar, assignments } <- CVar.genWithAssignments pf
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
            if b' then (scale_ (recip b) cvar)
            else add_ cvar (scale_ (-one) cvar)
      pure { basic: Boolean cvar', assignments }

    genEqual = do
      { cvar: left, assignments: a1 } <- CVar.genWithAssignments pf
      { cvar: right, assignments: a2 } <- CVar.genWithAssignments pf
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
        Left (e :: EvaluationError f) -> unsafeCrashWith $ "Unexpected error when generating r1cs: " <> show e
        Right right' ->
          pure
            { basic: Equal left right'
            , assignments
            }

    genR1CS = do
      { cvar: left, assignments: a1 } <- CVar.genWithAssignments pf
      { cvar: right, assignments: a2 } <- CVar.genWithAssignments pf
      { cvar: output, assignments: a3 } <- CVar.genWithAssignments pf
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
