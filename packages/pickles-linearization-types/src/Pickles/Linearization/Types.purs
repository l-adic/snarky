module Pickles.Linearization.Types
  ( -- Gate and column types (needed for FFI/testing)
    GateType(..)
  , LookupPattern(..)
  , FeatureFlag(..)
  , Column(..)
  , CurrOrNext(..)
  , ChallengeTerm(..)
  , ConstantTerm(..)
  , RowOffset
  , IndexTerm(..)
  , Linearization
  -- Opaque linearization polynomial
  , LinearizationPoly
  -- Internal: only for Pallas/Vesta/Interpreter modules
  , PolishToken(..)
  , mkLinearizationPoly
  , runLinearizationPoly
  ) where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Foreign (F, Foreign, ForeignError(..), fail, readArray, readBoolean, readInt, readString)
import Foreign.Index (readProp)
import Simple.JSON (class ReadForeign, readImpl)

-- | Gate types used in Index columns
data GateType
  = CompleteAdd
  | EndoMul
  | EndoMulScalar
  | ForeignFieldAdd
  | ForeignFieldMul
  | Generic
  | Poseidon
  | RangeCheck0
  | RangeCheck1
  | Rot64
  | VarBaseMul
  | Xor16

derive instance Eq GateType
derive instance Ord GateType

instance Show GateType where
  show = case _ of
    CompleteAdd -> "CompleteAdd"
    EndoMul -> "EndoMul"
    EndoMulScalar -> "EndoMulScalar"
    ForeignFieldAdd -> "ForeignFieldAdd"
    ForeignFieldMul -> "ForeignFieldMul"
    Generic -> "Generic"
    Poseidon -> "Poseidon"
    RangeCheck0 -> "RangeCheck0"
    RangeCheck1 -> "RangeCheck1"
    Rot64 -> "Rot64"
    VarBaseMul -> "VarBaseMul"
    Xor16 -> "Xor16"

instance ReadForeign GateType where
  readImpl f = do
    str <- readString f
    case str of
      "CompleteAdd" -> pure CompleteAdd
      "EndoMul" -> pure EndoMul
      "EndoMulScalar" -> pure EndoMulScalar
      "ForeignFieldAdd" -> pure ForeignFieldAdd
      "ForeignFieldMul" -> pure ForeignFieldMul
      "Generic" -> pure Generic
      "Poseidon" -> pure Poseidon
      "RangeCheck0" -> pure RangeCheck0
      "RangeCheck1" -> pure RangeCheck1
      "Rot64" -> pure Rot64
      "VarBaseMul" -> pure VarBaseMul
      "Xor16" -> pure Xor16
      other -> err $ "Unknown GateType: " <> other

-- | Lookup pattern types
data LookupPattern
  = LookupPatternXor
  | LookupPatternLookup
  | LookupPatternRangeCheck
  | LookupPatternForeignFieldMul

derive instance Eq LookupPattern
derive instance Ord LookupPattern

instance Show LookupPattern where
  show = case _ of
    LookupPatternXor -> "Xor"
    LookupPatternLookup -> "Lookup"
    LookupPatternRangeCheck -> "RangeCheck"
    LookupPatternForeignFieldMul -> "ForeignFieldMul"

instance ReadForeign LookupPattern where
  readImpl f = do
    str <- readString f
    case str of
      "Xor" -> pure LookupPatternXor
      "Lookup" -> pure LookupPatternLookup
      "RangeCheck" -> pure LookupPatternRangeCheck
      "ForeignFieldMul" -> pure LookupPatternForeignFieldMul
      other -> err $ "Unknown LookupPattern: " <> other

-- | Feature flags for conditional evaluation
data FeatureFlag
  = FeatureForeignFieldAdd
  | FeatureForeignFieldMul
  | FeatureLookupTables
  | FeatureRangeCheck0
  | FeatureRangeCheck1
  | FeatureRot
  | FeatureRuntimeLookupTables
  | FeatureXor
  | FeatureLookupPattern LookupPattern
  | FeatureLookupsPerRow Int
  | FeatureTableWidth Int

derive instance Eq FeatureFlag
derive instance Ord FeatureFlag

instance Show FeatureFlag where
  show = case _ of
    FeatureForeignFieldAdd -> "ForeignFieldAdd"
    FeatureForeignFieldMul -> "ForeignFieldMul"
    FeatureLookupTables -> "LookupTables"
    FeatureRangeCheck0 -> "RangeCheck0"
    FeatureRangeCheck1 -> "RangeCheck1"
    FeatureRot -> "Rot"
    FeatureRuntimeLookupTables -> "RuntimeLookupTables"
    FeatureXor -> "Xor"
    FeatureLookupPattern p -> "LookupPattern(" <> show p <> ")"
    FeatureLookupsPerRow n -> "LookupsPerRow(" <> show n <> ")"
    FeatureTableWidth n -> "TableWidth(" <> show n <> ")"

instance ReadForeign FeatureFlag where
  readImpl f = readAsString <|> readAsObject
    where
    readAsString = do
      str <- readString f
      case str of
        "ForeignFieldAdd" -> pure FeatureForeignFieldAdd
        "ForeignFieldMul" -> pure FeatureForeignFieldMul
        "LookupTables" -> pure FeatureLookupTables
        "RangeCheck0" -> pure FeatureRangeCheck0
        "RangeCheck1" -> pure FeatureRangeCheck1
        "Rot" -> pure FeatureRot
        "RuntimeLookupTables" -> pure FeatureRuntimeLookupTables
        "Xor" -> pure FeatureXor
        other -> err $ "Unknown FeatureFlag: " <> other

    readAsObject =
      (FeatureLookupPattern <$> (readProp "LookupPattern" f >>= readImpl))
        <|> (FeatureLookupsPerRow <$> (readProp "LookupsPerRow" f >>= readInt))
        <|> (FeatureTableWidth <$> (readProp "TableWidth" f >>= readInt))

-- | Column types in the constraint system
data Column
  = Witness Int
  | Coefficient Int
  | Index GateType
  | LookupAggreg
  | LookupKindIndex Int
  | LookupRuntimeSelector
  | LookupRuntimeTable
  | LookupSorted Int
  | LookupTable

derive instance Eq Column
derive instance Ord Column

instance Show Column where
  show = case _ of
    Witness i -> "Witness(" <> show i <> ")"
    Coefficient i -> "Coefficient(" <> show i <> ")"
    Index g -> "Index(" <> show g <> ")"
    LookupAggreg -> "LookupAggreg"
    LookupKindIndex i -> "LookupKindIndex(" <> show i <> ")"
    LookupRuntimeSelector -> "LookupRuntimeSelector"
    LookupRuntimeTable -> "LookupRuntimeTable"
    LookupSorted i -> "LookupSorted(" <> show i <> ")"
    LookupTable -> "LookupTable"

instance ReadForeign Column where
  readImpl f =
    (Witness <$> (readProp "Witness" f >>= readInt))
      <|> (Coefficient <$> (readProp "Coefficient" f >>= readInt))
      <|> (Index <$> (readProp "Index" f >>= readImpl))
      <|> (LookupKindIndex <$> (readProp "LookupKindIndex" f >>= readInt))
      <|> (LookupSorted <$> (readProp "LookupSorted" f >>= readInt))
      <|> readUnitVariant "LookupAggreg" LookupAggreg f
      <|> readUnitVariant "LookupRuntimeSelector" LookupRuntimeSelector f
      <|> readUnitVariant "LookupRuntimeTable" LookupRuntimeTable f
      <|> readUnitVariant "LookupTable" LookupTable f

-- | Row offset (current or next)
data CurrOrNext = Curr | Next

derive instance Eq CurrOrNext
derive instance Ord CurrOrNext

instance Show CurrOrNext where
  show Curr = "Curr"
  show Next = "Next"

instance ReadForeign CurrOrNext where
  readImpl f = do
    str <- readString f
    case str of
      "Curr" -> pure Curr
      "Next" -> pure Next
      other -> err $ "Unknown CurrOrNext: " <> other

-- | Challenge terms from the transcript
data ChallengeTerm
  = Alpha
  | Beta
  | Gamma
  | JointCombiner

derive instance Eq ChallengeTerm
derive instance Ord ChallengeTerm

instance Show ChallengeTerm where
  show = case _ of
    Alpha -> "Alpha"
    Beta -> "Beta"
    Gamma -> "Gamma"
    JointCombiner -> "JointCombiner"

instance ReadForeign ChallengeTerm where
  readImpl f = do
    str <- readString f
    case str of
      "Alpha" -> pure Alpha
      "Beta" -> pure Beta
      "Gamma" -> pure Gamma
      "JointCombiner" -> pure JointCombiner
      other -> err $ "Unknown ChallengeTerm: " <> other

-- | Row offset for Lagrange basis
type RowOffset =
  { zk_rows :: Boolean
  , offset :: Int
  }

-- | Constant terms in the constraint expression
data ConstantTerm
  = EndoCoefficient
  | Mds { row :: Int, col :: Int }
  | Literal String -- Hex string representation

derive instance Eq ConstantTerm
derive instance Ord ConstantTerm

instance Show ConstantTerm where
  show = case _ of
    EndoCoefficient -> "EndoCoefficient"
    Mds { row, col } -> "Mds(" <> show row <> "," <> show col <> ")"
    Literal s -> "Literal(" <> s <> ")"

instance ReadForeign ConstantTerm where
  readImpl f = readAsString <|> readAsObject
    where
    readAsString = do
      str <- readString f
      case str of
        "EndoCoefficient" -> pure EndoCoefficient
        other -> err $ "Unknown ConstantTerm: " <> other

    readAsObject =
      ( do
          mdsObj <- readProp "Mds" f
          row <- readProp "row" mdsObj >>= readInt
          col <- readProp "col" mdsObj >>= readInt
          pure $ Mds { row, col }
      )
        <|> (Literal <$> (readProp "Literal" f >>= readString))

-- | Polish notation tokens for expression evaluation
data PolishToken
  = Constant ConstantTerm
  | Challenge ChallengeTerm
  | Cell { col :: Column, row :: CurrOrNext }
  | Dup
  | Pow Int
  | Add
  | Mul
  | Sub
  | VanishesOnZeroKnowledgeAndPreviousRows
  | UnnormalizedLagrangeBasis RowOffset
  | Store
  | Load Int
  | SkipIf FeatureFlag Int
  | SkipIfNot FeatureFlag Int

derive instance Eq PolishToken
derive instance Ord PolishToken

instance Show PolishToken where
  show = case _ of
    Constant c -> "Constant(" <> show c <> ")"
    Challenge c -> "Challenge(" <> show c <> ")"
    Cell { col, row } -> "Cell(" <> show col <> "," <> show row <> ")"
    Dup -> "Dup"
    Pow n -> "Pow(" <> show n <> ")"
    Add -> "Add"
    Mul -> "Mul"
    Sub -> "Sub"
    VanishesOnZeroKnowledgeAndPreviousRows -> "VanishesOnZeroKnowledgeAndPreviousRows"
    UnnormalizedLagrangeBasis r -> "UnnormalizedLagrangeBasis(" <> show r <> ")"
    Store -> "Store"
    Load n -> "Load(" <> show n <> ")"
    SkipIf f n -> "SkipIf(" <> show f <> "," <> show n <> ")"
    SkipIfNot f n -> "SkipIfNot(" <> show f <> "," <> show n <> ")"

instance ReadForeign PolishToken where
  readImpl f = readAsString <|> readAsObject
    where
    readAsString = do
      str <- readString f
      case str of
        "Dup" -> pure Dup
        "Add" -> pure Add
        "Mul" -> pure Mul
        "Sub" -> pure Sub
        "Store" -> pure Store
        "VanishesOnZeroKnowledgeAndPreviousRows" -> pure VanishesOnZeroKnowledgeAndPreviousRows
        other -> err $ "Unknown PolishToken: " <> other

    readAsObject =
      (Constant <$> (readProp "Constant" f >>= readImpl))
        <|> (Challenge <$> (readProp "Challenge" f >>= readImpl))
        <|> readCell
        <|> (Pow <$> (readProp "Pow" f >>= readInt))
        <|> readUnnormalizedLagrangeBasis
        <|> (Load <$> (readProp "Load" f >>= readInt))
        <|> readSkipIf
        <|> readSkipIfNot

    readCell = do
      cellObj <- readProp "Cell" f
      col <- readProp "col" cellObj >>= readImpl
      row <- readProp "row" cellObj >>= readImpl
      pure $ Cell { col, row }

    readUnnormalizedLagrangeBasis = do
      obj <- readProp "UnnormalizedLagrangeBasis" f
      zk_rows <- readProp "zk_rows" obj >>= readBoolean
      offset <- readProp "offset" obj >>= readInt
      pure $ UnnormalizedLagrangeBasis { zk_rows, offset }

    readSkipIf = do
      arr <- readProp "SkipIf" f >>= readArray
      case Array.uncons arr of
        Just { head: flagF, tail } -> case Array.uncons tail of
          Just { head: countF, tail: [] } -> do
            flag <- readImpl flagF
            count <- readInt countF
            pure $ SkipIf flag count
          _ -> err "SkipIf expects exactly 2 elements"
        Nothing -> err "SkipIf expects exactly 2 elements"

    readSkipIfNot = do
      arr <- readProp "SkipIfNot" f >>= readArray
      case Array.uncons arr of
        Just { head: flagF, tail } -> case Array.uncons tail of
          Just { head: countF, tail: [] } -> do
            flag <- readImpl flagF
            count <- readInt countF
            pure $ SkipIfNot flag count
          _ -> err "SkipIfNot expects exactly 2 elements"
        Nothing -> err "SkipIfNot expects exactly 2 elements"

-- | An index term is a tuple of (Column, Array PolishToken) serialized as a 2-element JSON array
newtype IndexTerm = IndexTerm (Tuple Column (Array PolishToken))

derive instance Eq IndexTerm
derive instance Ord IndexTerm

instance Show IndexTerm where
  show (IndexTerm (Tuple col tokens)) = "IndexTerm(" <> show col <> ", " <> show tokens <> ")"

instance ReadForeign IndexTerm where
  readImpl f = do
    arr <- readArray f
    case Array.uncons arr of
      Just { head: colF, tail } -> case Array.uncons tail of
        Just { head: tokensF, tail: [] } -> do
          col <- readImpl colF
          tokens <- readImpl tokensF
          pure $ IndexTerm (Tuple col tokens)
        _ -> err "IndexTerm expects exactly 2 elements"
      Nothing -> err "IndexTerm expects exactly 2 elements"

-- | The linearization structure
type Linearization =
  { constant_term :: Array PolishToken
  , index_terms :: Array IndexTerm
  }

-- | A linearization polynomial parameterized by the circuit field.
-- |
-- | The phantom type `f` indicates which field this linearization evaluates in:
-- | - `LinearizationPoly Vesta.ScalarField` for Pallas-based proofs (circuits on Fp)
-- | - `LinearizationPoly Pallas.ScalarField` for Vesta-based proofs (circuits on Fq)
-- |
-- | This is an opaque type - users cannot construct it directly.
-- | Use the pre-built linearizations from Pickles.Linearization.Pallas/Vesta.
newtype LinearizationPoly :: forall k. k -> Type
newtype LinearizationPoly f = LinearizationPoly (Array PolishToken)

-- | Internal: construct a linearization polynomial.
-- | Only for use by Pallas/Vesta modules.
mkLinearizationPoly :: forall f. Array PolishToken -> LinearizationPoly f
mkLinearizationPoly = LinearizationPoly

-- | Internal: unwrap to get the raw tokens.
-- | Only for use by Interpreter/GateConstraints modules.
runLinearizationPoly :: forall f. LinearizationPoly f -> Array PolishToken
runLinearizationPoly (LinearizationPoly tokens) = tokens

-- Helper to read unit variants that serialize as `{ "VariantName": null }`
readUnitVariant :: forall a. String -> a -> Foreign -> F a
readUnitVariant name ctor f = do
  _ <- readProp name f
  pure ctor

-- Helper to create a ForeignError
err :: forall a. String -> F a
err = fail <<< ForeignError
