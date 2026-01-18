module Pickles.Linearization.Generator
  ( generateModule
  , CurveName(..)
  ) where

import Prelude

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
  ( declImport
  , declSignature
  , declValue
  , defaultPrintOptions
  , exprApp
  , exprArray
  , exprBool
  , exprCtor
  , exprInt
  , exprRecord
  , exprString
  , importTypeAll
  , module_
  , printModuleWithOptions
  , typeApp
  , typeCtor
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
  printOptions = defaultPrintOptions { pageWidth = 120, ribbonRatio = 1.0 }

-- | Build the CST module
buildModule :: Partial => CurveName -> Linearization -> Module Void
buildModule curve lin =
  module_ moduleName [] imports decls
  where
  curveStr = show curve
  moduleName = "Pickles.Linearization." <> curveStr

  imports =
    [ declImport "Prelude" [] -- For negate (used by negative integer literals)
    , declImport "Pickles.Linearization.Types"
        [ importTypeAll "PolishToken"
        , importTypeAll "ChallengeTerm"
        , importTypeAll "Column"
        , importTypeAll "ConstantTerm"
        , importTypeAll "CurrOrNext"
        , importTypeAll "FeatureFlag"
        , importTypeAll "GateType"
        , importTypeAll "LookupPattern"
        ]
    ]

  -- Convert all tokens to expressions
  tokenExprs = map tokenExpr lin.constant_term

  decls =
    [ declSignature "constantTermTokens"
        (typeApp (typeCtor "Array") [ typeCtor "PolishToken" ])
    , declValue "constantTermTokens" [] (exprArray tokenExprs)
    ]

-- | Convert a PolishToken to an Expr
tokenExpr :: Partial => PolishToken -> Expr Void
tokenExpr = case _ of
  -- Constants
  Constant EndoCoefficient ->
    exprApp (exprCtor "Constant") [ exprCtor "EndoCoefficient" ]

  Constant (Mds { row, col }) ->
    exprApp (exprCtor "Constant")
      [ exprApp (exprCtor "Mds")
          [ exprRecord [ Tuple "row" (exprInt row), Tuple "col" (exprInt col) ] ]
      ]

  Constant (Literal lit) ->
    exprApp (exprCtor "Constant") [ exprApp (exprCtor "Literal") [ exprString lit ] ]

  -- Challenges
  Challenge Alpha -> exprApp (exprCtor "Challenge") [ exprCtor "Alpha" ]
  Challenge Beta -> exprApp (exprCtor "Challenge") [ exprCtor "Beta" ]
  Challenge Gamma -> exprApp (exprCtor "Challenge") [ exprCtor "Gamma" ]
  Challenge JointCombiner -> exprApp (exprCtor "Challenge") [ exprCtor "JointCombiner" ]

  -- Cell access
  Cell { col, row } ->
    exprApp (exprCtor "Cell")
      [ exprRecord [ Tuple "col" (columnExpr col), Tuple "row" (rowExpr row) ] ]

  -- Stack operations
  Dup -> exprCtor "Dup"

  -- Arithmetic
  Add -> exprCtor "Add"
  Mul -> exprCtor "Mul"
  Sub -> exprCtor "Sub"
  Pow n -> exprApp (exprCtor "Pow") [ exprInt n ]

  -- Store/Load
  Store -> exprCtor "Store"
  Load n -> exprApp (exprCtor "Load") [ exprInt n ]

  -- Special terms
  VanishesOnZeroKnowledgeAndPreviousRows -> exprCtor "VanishesOnZeroKnowledgeAndPreviousRows"

  UnnormalizedLagrangeBasis { zk_rows, offset } ->
    exprApp (exprCtor "UnnormalizedLagrangeBasis")
      [ exprRecord
          [ Tuple "zk_rows" (exprBool zk_rows)
          , Tuple "offset" (exprInt offset)
          ]
      ]

  -- Conditional execution
  SkipIfNot flag count ->
    exprApp (exprCtor "SkipIfNot") [ featureFlagExpr flag, exprInt count ]

  SkipIf flag count ->
    exprApp (exprCtor "SkipIf") [ featureFlagExpr flag, exprInt count ]

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
