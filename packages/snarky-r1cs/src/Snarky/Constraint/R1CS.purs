module Snarky.Constraint.R1CS
  ( R1CS(..)
  , collectVariables
  , genWithAssignments
  , eval
  , classifyVariables
  ) where

import Prelude

import Data.Foldable (foldMap, foldl)
import Data.Map (Map)
import Data.Set (Set)
import Data.Set as Set
import Snarky.Circuit.CVar (CVar, Variable, const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

newtype R1CS f = R1CS { left :: (CVar f Variable), right :: (CVar f Variable), output :: (CVar f Variable) }

derive newtype instance Show f => Show (R1CS f)

collectVariables :: forall f. R1CS f -> Set Variable
collectVariables (R1CS { left, right, output }) =
  let
    f = foldl (flip Set.insert) mempty
  in
    foldMap f [ left, right, output ]

genWithAssignments
  :: forall f
   . PrimeField f
  => Proxy f
  -> Gen
       { r1cs :: R1CS f
       , assignments :: Map Variable f
       }
genWithAssignments pf =
  Basic.genWithAssignments pf <#> \{ basic, assignments } ->
    { r1cs: Basic.fromBasic basic
    , assignments
    }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> R1CS f
  -> m Boolean
eval lookup (R1CS c) = ado
  left <- CVar.eval lookup c.left
  right <- CVar.eval lookup c.right
  output <- CVar.eval lookup c.output
  in left * right == output

instance PrimeField f => Basic.BasicSystem f (R1CS f) where
  r1cs { left, right, output } = R1CS { left, right, output }
  boolean v = R1CS { left: v, right: v, output: v }
  -- NB: DO NOT CHANGE THIS TO 1 * (a - b) = zero
  equal a b = R1CS { left: a, right: const_ one, output: b }

classifyVariables
  :: forall f
   . PrimeField f
  => Array Variable
  -> Array (R1CS f)
  -> { privateInputs :: Array Variable
     , gateOutputs :: Array Variable
     }
classifyVariables publicInputs constraints =
  let
    gather = foldl (flip Set.insert) mempty
    vs =
      foldl
        ( \acc (R1CS { left, right, output }) ->
            let
              outputs = gather output
            in
              acc
                { vars = acc.vars <> gather left <> gather right <> outputs
                , outputs = acc.outputs <> outputs
                }
        )
        { vars: mempty, outputs: mempty }
        constraints
    privateInputs = vs.vars `Set.difference` (vs.outputs `Set.union` (Set.fromFoldable publicInputs))
  in
    { privateInputs: Set.toUnfoldable privateInputs
    , gateOutputs: Set.toUnfoldable vs.outputs
    }