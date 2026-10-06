module Test.Snarky.Circuit.Kimchi.InternalVariables
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Map as Map
import Data.Maybe (fromMaybe, isJust, maybe)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray, internalVariables)
import Snarky.Backend.Compile (compile', makeSolver')
import Snarky.Circuit.CVar (EvaluationError, Variable(..))
import Snarky.Circuit.DSL (F(..), FVar, Snarky, add_, const_, mul_, scale_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState, KimchiRow, toKimchiRows)
import Snarky.Curves.Class (fromInt)
import Snarky.Curves.Pallas as Pallas
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Type.Proxy (Proxy(..))

type F' = F Pallas.BaseField
type FV = FVar Pallas.BaseField
type KC = KimchiConstraint Pallas.BaseField
type Circuit = Tuple FV FV -> Snarky Pallas.BaseField KC () FV
type Compiled = CircuitBuilderState (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)

-- | Products of linear combinations: every factor, and the output,
-- | reduces to an internal variable.
circuit :: Circuit
circuit (Tuple a b) = do
  c <- mul_ (a `add_` b) (scale_ (fromInt 3) a `sub_` b)
  d <- mul_ (c `add_` const_ one) (a `add_` scale_ (fromInt 2) c)
  pure (d `add_` b)

-- | `circuit` without its second product.
shorter :: Circuit
shorter (Tuple a b) = do
  c <- mul_ (a `add_` b) (scale_ (fromInt 3) a `sub_` b)
  pure (c `add_` b)

compileIt :: Circuit -> Effect Compiled
compileIt = compile' noAdvice { debug: false } (Proxy @(Tuple F' F')) (Proxy @F') (Proxy @KC)

-- | Solve a circuit at a fixed input, against a compile.
solve :: Compiled -> Circuit -> Effect (Either EvaluationError (Tuple F' (Assignments.Frozen Pallas.BaseField)))
solve compiled c =
  makeSolver' { debug: false } compiled c noAdvice (Tuple (F (fromInt 7)) (F (fromInt 11)))

-- | Whether the assignments satisfy a generic row: each half reads
-- | cl·l + cr·r + co·o + m·l·r + c = 0, an absent variable counting as
-- | zero. A row without coefficients holds.
rowHolds :: Assignments.Frozen Pallas.BaseField -> KimchiRow Pallas.BaseField -> Boolean
rowHolds frozen { coeffs, variables } =
  Array.all identity (Array.zipWith halfHolds (Vector.chunk 5 coeffs) (Vector.chunk 3 (Vector.toUnfoldable variables)))
  where
  value = maybe zero \v -> fromMaybe zero (Assignments.lookupFrozen v frozen)
  halfHolds [ cl, cr, co, m, c ] [ vl, vr, vo ] =
    cl * value vl + cr * value vr + co * value vo + m * value vl * value vr + c == zero
  halfHolds _ _ = false

spec :: Spec Unit
spec = describe "internal variables" do
  it "a solve assigns them so that the compiled rows hold" do
    compiled <- liftEffect (compileIt circuit)
    Map.size (internalVariables compiled) `shouldSatisfy` (_ > 0)
    liftEffect (solve compiled circuit) >>= case _ of
      Left e -> fail (show e)
      Right (Tuple out frozen) -> do
        let
          Variable numVars = compiled.nextVar
          rows = Array.concatMap (toKimchiRows <<< _.constraint) (constraintsToArray compiled.constraints)
        -- c = (7 + 11)(21 − 11) = 180, d = (180 + 1)(7 + 360) = 66427
        out `shouldEqual` F (fromInt 66438)
        map (\i -> Assignments.lookupFrozen (Variable i) frozen) (Array.range 0 (numVars - 1))
          `shouldSatisfy` Array.all isJust
        Array.length rows `shouldSatisfy` (_ > 0)
        rows `shouldSatisfy` Array.all (rowHolds frozen)

  it "a solve against another circuit's compile fails" do
    compiled <- liftEffect (compileIt circuit)
    compiledShorter <- liftEffect (compileIt shorter)
    longer <- liftEffect (solve compiledShorter circuit)
    isLeft longer `shouldEqual` true
    fewer <- liftEffect (solve compiled shorter)
    isLeft fewer `shouldEqual` true
