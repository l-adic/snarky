module Pickles.Linearization.Generator
  ( generateModule
  , CurveName(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types
  ( ChallengeTerm(..)
  , Column(..)
  , ConstantTerm(..)
  , CurrOrNext(..)
  , GateType(..)
  , Linearization
  , PolishToken(..)
  )
import PureScript.CST.Types (Expr, Module)
import Tidy.Codegen
  ( binderRecord
  , binderVar
  , declImport
  , declSignature
  , declValue
  , exprApp
  , exprBool
  , exprCtor
  , exprIdent
  , exprInt
  , exprLet
  , exprRecord
  , exprString
  , importTypeAll
  , letValue
  , module_
  , printModule
  , typeApp
  , typeArrow
  , typeCtor
  , typeForall
  , typeVar
  )

-- | Which curve's linearization we're generating for
data CurveName = Pallas | Vesta

derive instance Eq CurveName

instance Show CurveName where
  show Pallas = "Pallas"
  show Vesta = "Vesta"

-- | Generate a complete PureScript module for a linearization
generateModule :: CurveName -> Linearization -> String
generateModule curve lin =
  unsafePartial $ printModule $ buildModule curve lin

-- | Evaluation state during Polish notation processing
type EvalState =
  { stack :: Array (Expr Void) -- Expression stack
  , store :: Array (Expr Void) -- Stored values (for Load)
  , bindings :: Array { name :: String, expr :: Expr Void } -- Let bindings to emit
  , nextVar :: Int -- Next variable number for bindings
  }

initialState :: EvalState
initialState = { stack: [], store: [], bindings: [], nextVar: 0 }

-- | Push an expression onto the stack
push :: Expr Void -> EvalState -> EvalState
push e s = s { stack = Array.snoc s.stack e }

-- | Pop an expression from the stack
pop :: EvalState -> Maybe { expr :: Expr Void, state :: EvalState }
pop s = do
  { init, last } <- Array.unsnoc s.stack
  pure { expr: last, state: s { stack = init } }

-- | Pop two expressions (for binary ops)
pop2 :: EvalState -> Maybe { left :: Expr Void, right :: Expr Void, state :: EvalState }
pop2 s = do
  { expr: right, state: s1 } <- pop s
  { expr: left, state: s2 } <- pop s1
  pure { left, right, state: s2 }

-- | Build the CST module
buildModule :: Partial => CurveName -> Linearization -> Module Void
buildModule curve lin =
  module_ moduleName [] imports decls
  where
  curveStr = show curve
  moduleName = "Snarky.Pickles.Linearization." <> curveStr

  imports =
    [ declImport "Prelude" []
    , declImport "Snarky.Pickles.Linearization.Env"
        [ importTypeAll "Env"
        , importTypeAll "Column"
        , importTypeAll "CurrOrNext"
        , importTypeAll "GateType"
        ]
    ]

  -- Generate the constant_term function
  constantTermExpr = evaluatePolish lin.constant_term

  decls =
    [ declSignature "constantTerm"
        ( typeForall [ typeVar "a" ]
            (typeArrow [ typeApp (typeCtor "Env") [ typeVar "a" ] ] (typeVar "a"))
        )
    , declValue "constantTerm" [ envBinder ] constantTermExpr
    ]

  -- Pattern match on the Env record to extract operations
  envBinder = binderRecord
    [ Tuple "add" (binderVar "add")
    , Tuple "sub" (binderVar "sub")
    , Tuple "mul" (binderVar "mul")
    , Tuple "pow" (binderVar "pow")
    , Tuple "var" (binderVar "var")
    , Tuple "cell" (binderVar "cell")
    , Tuple "alphaPow" (binderVar "alphaPow")
    , Tuple "mds" (binderVar "mds")
    , Tuple "endoCoefficient" (binderVar "endoCoefficient")
    , Tuple "field" (binderVar "field")
    , Tuple "vanishesOnZeroKnowledgeAndPreviousRows" (binderVar "vanishesOnZeroKnowledgeAndPreviousRows")
    , Tuple "unnormalizedLagrangeBasis" (binderVar "unnormalizedLagrangeBasis")
    , Tuple "jointCombiner" (binderVar "jointCombiner")
    , Tuple "beta" (binderVar "beta")
    , Tuple "gamma" (binderVar "gamma")
    , Tuple "ifFeature" (binderVar "ifFeature")
    ]

-- | Evaluate Polish notation tokens to produce an expression
evaluatePolish :: Partial => Array PolishToken -> Expr Void
evaluatePolish tokens =
  let
    finalState = foldl evalToken initialState tokens
  in
    case Array.last finalState.stack of
      Just result -> wrapWithBindings finalState.bindings result
      Nothing -> exprIdent "mempty" -- Empty expression

-- | Wrap an expression with let bindings
wrapWithBindings :: Partial => Array { name :: String, expr :: Expr Void } -> Expr Void -> Expr Void
wrapWithBindings bindings body =
  case Array.uncons bindings of
    Nothing -> body
    Just { head: b, tail: rest } ->
      exprLet [ letValue b.name [] b.expr ] (wrapWithBindings rest body)

-- | Evaluate a single token
evalToken :: Partial => EvalState -> PolishToken -> EvalState
evalToken s = case _ of
  -- Constants
  Constant EndoCoefficient ->
    push (exprIdent "endoCoefficient") s

  Constant (Mds { row, col }) ->
    push (exprApp (exprIdent "mds") [ exprRecord [ Tuple "row" (exprInt row), Tuple "col" (exprInt col) ] ]) s

  Constant (Literal lit) ->
    push (exprApp (exprIdent "field") [ exprString lit ]) s

  -- Challenges
  Challenge Alpha -> push (exprApp (exprIdent "alphaPow") [ exprInt 1 ]) s
  Challenge Beta -> push (exprIdent "beta") s
  Challenge Gamma -> push (exprIdent "gamma") s
  Challenge JointCombiner -> push (exprIdent "jointCombiner") s

  -- Cell access
  Cell { col, row } ->
    push (exprApp (exprIdent "cell") [ exprApp (exprIdent "var") [ columnExpr col, rowExpr row ] ]) s

  -- Stack operations
  Dup ->
    case Array.last s.stack of
      Just top -> push top s
      Nothing -> s

  -- Arithmetic
  Add ->
    case pop2 s of
      Just { left, right, state } ->
        push (exprApp (exprIdent "add") [ left, right ]) state
      Nothing -> s

  Mul ->
    case pop2 s of
      Just { left, right, state } ->
        push (exprApp (exprIdent "mul") [ left, right ]) state
      Nothing -> s

  Sub ->
    case pop2 s of
      Just { left, right, state } ->
        push (exprApp (exprIdent "sub") [ left, right ]) state
      Nothing -> s

  Pow n ->
    case pop s of
      Just { expr, state } ->
        push (exprApp (exprIdent "pow") [ expr, exprInt n ]) state
      Nothing -> s

  -- Store/Load for sharing subexpressions
  Store ->
    case pop s of
      Just { expr, state } ->
        let
          varName = "x_" <> show state.nextVar
          newState = state
            { store = Array.snoc state.store (exprIdent varName)
            , bindings = Array.snoc state.bindings { name: varName, expr }
            , nextVar = state.nextVar + 1
            }
        in
          push (exprIdent varName) newState
      Nothing -> s

  Load n ->
    case Array.index s.store n of
      Just storedExpr -> push storedExpr s
      Nothing -> s

  -- Special terms
  VanishesOnZeroKnowledgeAndPreviousRows ->
    push (exprIdent "vanishesOnZeroKnowledgeAndPreviousRows") s

  UnnormalizedLagrangeBasis { zk_rows, offset } ->
    push
      ( exprApp (exprIdent "unnormalizedLagrangeBasis")
          [ exprRecord
              [ Tuple "zkRows" (exprBool zk_rows)
              , Tuple "offset" (exprInt offset)
              ]
          ]
      )
      s

  -- Conditional execution (TODO: proper implementation needs token lookahead)
  SkipIf _ _ -> s
  SkipIfNot _ _ -> s

-- | Generate expression for Column
columnExpr :: Partial => Column -> Expr Void
columnExpr = case _ of
  Witness i -> exprApp (exprCtor "Witness") [ exprInt i ]
  Coefficient i -> exprApp (exprCtor "Coefficient") [ exprInt i ]
  Index g -> exprApp (exprCtor "Index") [ gateTypeExpr g ]
  LookupAggreg -> exprCtor "LookupAggreg"
  LookupKindIndex i -> exprApp (exprCtor "LookupKindIndex") [ exprInt i ]
  LookupRuntimeSelector -> exprCtor "LookupRuntimeSelector"
  LookupRuntimeTable -> exprCtor "LookupRuntimeTable"
  LookupSorted i -> exprApp (exprCtor "LookupSorted") [ exprInt i ]
  LookupTable -> exprCtor "LookupTable"

-- | Generate expression for GateType
gateTypeExpr :: Partial => GateType -> Expr Void
gateTypeExpr = case _ of
  CompleteAdd -> exprCtor "CompleteAdd"
  EndoMul -> exprCtor "EndoMul"
  EndoMulScalar -> exprCtor "EndoMulScalar"
  ForeignFieldAdd -> exprCtor "ForeignFieldAdd"
  ForeignFieldMul -> exprCtor "ForeignFieldMul"
  Generic -> exprCtor "Generic"
  Poseidon -> exprCtor "Poseidon"
  RangeCheck0 -> exprCtor "RangeCheck0"
  RangeCheck1 -> exprCtor "RangeCheck1"
  Rot64 -> exprCtor "Rot64"
  VarBaseMul -> exprCtor "VarBaseMul"
  Xor16 -> exprCtor "Xor16"

-- | Generate expression for CurrOrNext
rowExpr :: Partial => CurrOrNext -> Expr Void
rowExpr = case _ of
  Curr -> exprCtor "Curr"
  Next -> exprCtor "Next"
