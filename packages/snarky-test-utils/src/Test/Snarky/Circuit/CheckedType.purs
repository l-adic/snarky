module Test.Snarky.Circuit.CheckedType (spec) where

import Prelude

import Control.Apply (lift2)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Show.Generic (genericShow)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), Variable, const_)
import Snarky.Constraint.Basic (Basic)
import Snarky.Circuit.Types (class CheckedType, Bool, BoolVar, FVar, UnChecked(..), check, genericCheck)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary, (===))
import Test.QuickCheck.Gen (suchThat)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck')
import Type.Proxy (Proxy)

newtype ValidBVar f = ValidBVar (BoolVar f)

derive instance Newtype (ValidBVar f) _

instance PrimeField f => Arbitrary (ValidBVar f) where
  arbitrary = ValidBVar <$>

    let
      g :: CVar f (Bool Variable) -> Maybe f
      g = case _ of
        (Const x) -> Just x
        ScalarMul c v -> g v <#> \x -> x * c
        Add x y -> lift2 add (g x) (g y)
        (Var _) -> Nothing
    in
      arbitrary @(CVar f (Bool Variable)) `suchThat` \x -> case g x of
        Nothing -> true
        Just f -> f == zero || f == one

-- Custom datatype to test generic deriving
data Point f = Point f f

derive instance Generic (Point f) _
derive instance Eq f => Eq (Point f)

instance Show f => Show (Point f) where
  show = genericShow

instance Arbitrary f => Arbitrary (Point f) where
  arbitrary = Point <$> arbitrary <*> arbitrary

instance CheckedType (Point (CVar f Variable)) c where
  check = genericCheck

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec _ = do

  describe "CheckedType constraint tests" do

    it "F type has no constraints" $
      quickCheck' 10 \(value :: f) ->
        let
          cvar = const_ value :: CVar f Variable
          constraints = check @(CVar f Variable) @(Basic f) cvar
        in
          Array.null constraints === true

    it "Boolean type has exactly one constraint" $
      quickCheck' 10 \(cvar :: ValidBVar f) ->
        let
          constraints = check @(CVar f (Bool Variable)) @(Basic f) (un ValidBVar cvar)
        in
          Array.length constraints === 1

    it "Unit type has no constraints" $
      quickCheck' 10 \(_ :: Unit) ->
        let
          constraints = check @Unit @(Basic f) unit
        in
          Array.null constraints === true

    it "UnChecked F has no constraints" $
      quickCheck' 10 \(value :: f) ->
        let
          uncheckedVar = UnChecked (const_ value :: CVar f Variable)
          constraints = check @(UnChecked (CVar f Variable)) @(Basic f) uncheckedVar
        in
          Array.null constraints === true

    it "UnChecked Boolean has no constraints" $
      quickCheck' 10 \(x :: UnChecked (BoolVar f)) ->
        let
          constraints = check x
        in
          Array.null constraints === true

    -- Compound type constraint tests
    it "Record with F and Boolean accumulates constraints correctly" $
      quickCheck' 10 \(x :: { a :: FVar f, b :: ValidBVar f }) ->
        let
          constraints = check @_ @(Basic f) (coerce x :: { a :: FVar f, b :: BoolVar f })
        in
          Array.length constraints === 1 -- Only the Boolean should contribute a constraint

    it "Point with F fields has no constraints" $
      quickCheck' 10 \(x :: f) (y :: f) ->
        let
          point = Point (const_ x) (const_ y) :: Point (CVar f Variable)
          constraints = check @(Point (CVar f Variable)) @(Basic f) point
        in
          Array.null constraints === true

    it "Record with multiple Booleans accumulates all constraints" $
      quickCheck' 10 \(x :: { flag1 :: ValidBVar f, flag2 :: ValidBVar f }) ->
        let
          record :: { flag1 :: BoolVar f, flag2 :: BoolVar f }
          record = coerce x
          constraints = check @_ @(Basic f) record
        in
          Array.length constraints === 2 -- Both Booleans should contribute constraints
