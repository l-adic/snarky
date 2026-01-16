module Pickles.Linearization.Generator
  ( generateModule
  , CurveName(..)
  ) where

import Prelude

import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types
  ( ChallengeTerm(..)
  , Column(..)
  , ConstantTerm(..)
  , CurrOrNext(..)
  , FeatureFlag(..)
  , GateType(..)
  , Linearization
  , LookupPattern(..)
  , PolishToken(..)
  )
import PureScript.CST.Types (Expr, Module)
import Tidy.Codegen
  ( binderRecord
  , binderVar
  , declImport
  , declSignature
  , declValue
  , defaultPrintOptions
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
  , printModuleWithOptions
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
  unsafePartial $ printModuleWithOptions printOptions $ buildModule curve lin
  where
  -- Use a large page width to minimize line breaks
  printOptions = defaultPrintOptions { pageWidth = 100000 }

-- | Parser state for tracking stored values and let bindings
type ParseState =
  { store :: Array (Expr Void) -- Stored values (for Load)
  , bindings :: Array { name :: String, expr :: Expr Void } -- Let bindings to emit
  , nextVar :: Int -- Next variable number for bindings
  }

initialParseState :: ParseState
initialParseState = { store: [], bindings: [], nextVar: 0 }

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
        , importTypeAll "LookupPattern"
        , importTypeAll "FeatureFlag"
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

-- | Result of parsing: the expression stack and state
-- | We track two stacks: main expression stack and conditional expressions
type ParseResult =
  { stack :: Array (Expr Void) -- Main expression stack (RPN operations)
  , conditionals :: Array (Expr Void) -- Accumulated conditional (ifFeature) expressions
  , state :: ParseState
  }

-- | Evaluate Polish notation tokens to produce an expression
-- | Uses a recursive descent approach to handle SkipIf/SkipIfNot
evaluatePolish :: Partial => Array PolishToken -> Expr Void
evaluatePolish tokens =
  let
    tokenList = List.fromFoldable tokens
    result = evalTokens { stack: [], conditionals: [], state: initialParseState } tokenList
    -- The main result is the last value on the stack
    mainExpr = case Array.last result.stack of
      Just e -> e
      Nothing -> exprApp (exprIdent "field") [ exprString "0x0000000000000000000000000000000000000000000000000000000000000000" ]

    -- Combine the main expression with all conditional expressions using add
    -- This produces: add(mainExpr, add(cond1, add(cond2, ...)))
    combineWithConditionals :: Expr Void -> Array (Expr Void) -> Expr Void
    combineWithConditionals base conds = case Array.uncons conds of
      Nothing -> base
      Just { head: first, tail: rest } ->
        exprApp (exprIdent "add") [ base, combineWithConditionals first rest ]
  in
    wrapWithBindings result.state.bindings (combineWithConditionals mainExpr result.conditionals)

-- | Recursively evaluate tokens, returning updated stack and remaining tokens
evalTokens :: Partial => ParseResult -> List PolishToken -> ParseResult
evalTokens result Nil = result
evalTokens result (token : rest) =
  let
    newResult = evalToken result token rest
  in
    evalTokens newResult.result newResult.remaining

-- | Evaluate a single token, potentially consuming additional tokens for SkipIf/SkipIfNot
evalToken
  :: Partial
  => ParseResult
  -> PolishToken
  -> List PolishToken
  -> { result :: ParseResult, remaining :: List PolishToken }
evalToken r token remaining = case token of
  -- Constants
  Constant EndoCoefficient ->
    { result: pushStack (exprIdent "endoCoefficient") r, remaining }

  Constant (Mds { row, col }) ->
    { result: pushStack
        (exprApp (exprIdent "mds") [ exprRecord [ Tuple "row" (exprInt row), Tuple "col" (exprInt col) ] ])
        r
    , remaining
    }

  Constant (Literal lit) ->
    { result: pushStack (exprApp (exprIdent "field") [ exprString lit ]) r, remaining }

  -- Challenges
  Challenge Alpha -> { result: pushStack (exprApp (exprIdent "alphaPow") [ exprInt 1 ]) r, remaining }
  Challenge Beta -> { result: pushStack (exprIdent "beta") r, remaining }
  Challenge Gamma -> { result: pushStack (exprIdent "gamma") r, remaining }
  Challenge JointCombiner -> { result: pushStack (exprIdent "jointCombiner") r, remaining }

  -- Cell access
  Cell { col, row } ->
    { result: pushStack
        (exprApp (exprIdent "cell") [ exprApp (exprIdent "var") [ columnExpr col, rowExpr row ] ])
        r
    , remaining
    }

  -- Stack operations
  Dup ->
    case Array.last r.stack of
      Just top -> { result: pushStack top r, remaining }
      Nothing -> { result: r, remaining }

  -- Arithmetic
  Add ->
    case pop2Stack r of
      Just { left, right, result: r' } ->
        { result: pushStack (exprApp (exprIdent "add") [ left, right ]) r', remaining }
      Nothing -> { result: r, remaining }

  Mul ->
    case pop2Stack r of
      Just { left, right, result: r' } ->
        { result: pushStack (exprApp (exprIdent "mul") [ left, right ]) r', remaining }
      Nothing -> { result: r, remaining }

  Sub ->
    case pop2Stack r of
      Just { left, right, result: r' } ->
        { result: pushStack (exprApp (exprIdent "sub") [ left, right ]) r', remaining }
      Nothing -> { result: r, remaining }

  Pow n ->
    case popStack r of
      Just { expr, result: r' } ->
        { result: pushStack (exprApp (exprIdent "pow") [ expr, exprInt n ]) r', remaining }
      Nothing -> { result: r, remaining }

  -- Store/Load for sharing subexpressions
  Store ->
    case popStack r of
      Just { expr, result: r' } ->
        let
          varName = "x_" <> show r'.state.nextVar
          newState = r'.state
            { store = Array.snoc r'.state.store (exprIdent varName)
            , bindings = Array.snoc r'.state.bindings { name: varName, expr }
            , nextVar = r'.state.nextVar + 1
            }
        in
          { result: pushStack (exprIdent varName) (r' { state = newState }), remaining }
      Nothing -> { result: r, remaining }

  Load n ->
    case Array.index r.state.store n of
      Just storedExpr -> { result: pushStack storedExpr r, remaining }
      Nothing -> { result: r, remaining }

  -- Special terms
  VanishesOnZeroKnowledgeAndPreviousRows ->
    { result: pushStack (exprIdent "vanishesOnZeroKnowledgeAndPreviousRows") r, remaining }

  UnnormalizedLagrangeBasis { zk_rows, offset } ->
    { result: pushStack
        ( exprApp (exprIdent "unnormalizedLagrangeBasis")
            [ exprRecord
                [ Tuple "zkRows" (exprBool zk_rows)
                , Tuple "offset" (exprInt offset)
                ]
            ]
        )
        r
    , remaining
    }

  -- Conditional execution - SkipIfNot: if feature is NOT enabled, skip count tokens
  -- For code generation, we include the code wrapped in ifFeature
  --
  -- The sub-expression is evaluated and wrapped in ifFeature.
  -- Instead of pushing to the main stack (which would disrupt RPN flow),
  -- we add it to the conditionals list to be combined at the end.
  SkipIfNot flag count ->
    let
      -- Take 'count' tokens as the conditional sub-expression
      subTokens = List.take count remaining
      remainingAfter = List.drop count remaining
      -- Evaluate the sub-expression with empty stack - it's self-contained
      subResult = evalTokens { stack: [], conditionals: [], state: r.state } subTokens
      -- Get the result (what the block produces)
      subExpr = case Array.last subResult.stack of
        Just e -> e
        Nothing -> exprApp (exprIdent "field") [ exprString "0x0000000000000000000000000000000000000000000000000000000000000000" ]
      -- Wrap in ifFeature - onTrue is the sub-expression, onFalse is zero
      wrapped = exprApp (exprIdent "ifFeature")
        [ exprRecord
            [ Tuple "flag" (featureFlagExpr flag)
            , Tuple "onTrue" (exprApp (exprIdent "const") [ subExpr ])
            , Tuple "onFalse" (exprApp (exprIdent "const") ([ exprApp (exprIdent "field") [ exprString "0x0000000000000000000000000000000000000000000000000000000000000000" ] ]))
            ]
        ]
      -- Add only this wrapped expression to conditionals
      -- (nested conditionals are already inside the wrapped expression)
      newConditionals = Array.snoc r.conditionals wrapped
    in
      { result: r { conditionals = newConditionals, state = subResult.state }, remaining: remainingAfter }

  -- SkipIf: if feature IS enabled, skip count tokens (opposite of SkipIfNot)
  SkipIf flag count ->
    let
      subTokens = List.take count remaining
      remainingAfter = List.drop count remaining
      -- Evaluate with empty stack - sub-expression is self-contained
      subResult = evalTokens { stack: [], conditionals: [], state: r.state } subTokens
      subExpr = case Array.last subResult.stack of
        Just e -> e
        Nothing -> exprApp (exprIdent "field") [ exprString "0x0000000000000000000000000000000000000000000000000000000000000000" ]
      -- For SkipIf, onFalse has the expression (skip if true means execute if false)
      wrapped = exprApp (exprIdent "ifFeature")
        [ exprRecord
            [ Tuple "flag" (featureFlagExpr flag)
            , Tuple "onTrue" (exprApp (exprIdent "const") [ exprApp (exprIdent "field") [ exprString "0x0000000000000000000000000000000000000000000000000000000000000000" ] ])
            , Tuple "onFalse" (exprApp (exprIdent "const") [ subExpr ])
            ]
        ]
      -- Add only this wrapped expression to conditionals
      newConditionals = Array.snoc r.conditionals wrapped
    in
      { result: r { conditionals = newConditionals, state = subResult.state }, remaining: remainingAfter }

-- | Push onto stack
pushStack :: Expr Void -> ParseResult -> ParseResult
pushStack e r = r { stack = Array.snoc r.stack e }

-- | Pop from stack
popStack :: ParseResult -> Maybe { expr :: Expr Void, result :: ParseResult }
popStack r = do
  { init, last } <- Array.unsnoc r.stack
  pure { expr: last, result: r { stack = init } }

-- | Pop two from stack
pop2Stack :: ParseResult -> Maybe { left :: Expr Void, right :: Expr Void, result :: ParseResult }
pop2Stack r = do
  { expr: right, result: r1 } <- popStack r
  { expr: left, result: r2 } <- popStack r1
  pure { left, right, result: r2 }

-- | Wrap an expression with let bindings (single let block with all bindings)
wrapWithBindings :: Partial => Array { name :: String, expr :: Expr Void } -> Expr Void -> Expr Void
wrapWithBindings bindings body =
  case Array.length bindings of
    0 -> body
    _ -> exprLet (map (\b -> letValue b.name [] b.expr) bindings) body

-- | Generate expression for FeatureFlag
featureFlagExpr :: Partial => FeatureFlag -> Expr Void
featureFlagExpr = case _ of
  FeatureForeignFieldAdd -> exprCtor "FeatureForeignFieldAdd"
  FeatureForeignFieldMul -> exprCtor "FeatureForeignFieldMul"
  FeatureLookupTables -> exprCtor "FeatureLookupTables"
  FeatureRangeCheck0 -> exprCtor "FeatureRangeCheck0"
  FeatureRangeCheck1 -> exprCtor "FeatureRangeCheck1"
  FeatureRot -> exprCtor "FeatureRot"
  FeatureRuntimeLookupTables -> exprCtor "FeatureRuntimeLookupTables"
  FeatureXor -> exprCtor "FeatureXor"
  FeatureLookupPattern pat -> exprApp (exprCtor "FeatureLookupPattern") [ lookupPatternExpr pat ]
  FeatureLookupsPerRow n -> exprApp (exprCtor "FeatureLookupsPerRow") [ exprInt n ]
  FeatureTableWidth n -> exprApp (exprCtor "FeatureTableWidth") [ exprInt n ]

-- | Generate expression for LookupPattern
lookupPatternExpr :: Partial => LookupPattern -> Expr Void
lookupPatternExpr = case _ of
  LookupPatternXor -> exprCtor "LookupPatternXor"
  LookupPatternLookup -> exprCtor "LookupPatternLookup"
  LookupPatternRangeCheck -> exprCtor "LookupPatternRangeCheck"
  LookupPatternForeignFieldMul -> exprCtor "LookupPatternForeignFieldMul"

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
