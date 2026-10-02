-- | A compiled circuit's constraint system as the dumps carry it: per row
-- | its gate kind, wiring, variables, coefficients and labels.
module Pickles.Dump.Circuit
  ( Circuit
  , GateData
  , CachedConstant
  , comparable
  , fromCompiledCircuit
  ) where

import Prelude

import Data.Array (concatMap, replicate)
import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Pickles.CircuitDiffs.Types (ComparableCircuit)
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Kimchi (makeGateData)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, circuitGateGetWires)
import Snarky.Backend.Kimchi.Types (Gate, gateWiresGetWire, wireGetCol, wireGetRow)
import Snarky.Circuit.CVar (getVariable)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, modulus, toBigInt)

gateKindToString :: GateKind -> String
gateKindToString = case _ of
  Zero -> "Zero"
  GenericPlonkGate -> "Generic"
  PoseidonGate -> "Poseidon"
  AddCompleteGate -> "CompleteAdd"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoMulScalar"

-- | Convert a field element to a signed decimal string.
-- | Values > p/2 are shown as negative (e.g. p-1 becomes "-1").
toSignedDecimal :: forall f. PrimeField f => f -> String
toSignedDecimal x =
  let
    n = toBigInt x
    p = modulus @f
    half = p / BigInt.fromInt 2
  in
    if n > half then "-" <> BigInt.toString (p - n)
    else BigInt.toString n

-- | Convert variable vector to Maybe array.
-- | Returns Nothing if all variables are unset (e.g. OCaml-parsed gates).
varsToMaybe :: Vector 15 (Maybe Int) -> Maybe (Array Int)
varsToMaybe v =
  let
    arr = Vector.toUnfoldable v :: Array (Maybe Int)
    toInt = case _ of
      Nothing -> -1
      Just x -> x
  in
    if Array.all (_ == Nothing) arr then Nothing
    else Just (map toInt arr)

comparable :: forall f. Ord f => PrimeField f => SerdeHex f => Circuit f -> ComparableCircuit
comparable c =
  { publicInputSize: c.publicInputSize
  , gates: map
      ( \g ->
          { kind: gateKindToString g.kind
          , wires: g.wires
          , variables: varsToMaybe g.variables
          , coeffs: map toSignedDecimal g.coeffs
          , context: g.context
          }
      )
      c.gates
  , cachedConstants: Array.sortWith _.variable $ map (\cc -> { variable: cc.variable, varType: cc.varType, value: toSignedDecimal cc.value }) c.cachedConstants
  }

--------------------------------------------------------------------------------
-- Types

type GateData f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , variables :: Vector 15 (Maybe Int)
  , coeffs :: Array f
  , context :: Array String
  }

type CachedConstant f =
  { variable :: Int
  , varType :: String
  , value :: f
  }

type Circuit f =
  { publicInputSize :: Int
  , gates :: Array (GateData f)
  , cachedConstants :: Array (CachedConstant f)
  }

--------------------------------------------------------------------------------
-- From compiled PureScript circuit

-- | The one `makeGateData` of a compiled circuit.
gateDataOf
  :: forall f g
   . CircuitGateConstructor f g
  => PrimeField f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Effect
       { constraints :: Array (KimchiRow f)
       , gates :: Array (Gate f)
       , publicInputSize :: Int
       }
gateDataOf s = makeGateData @f
  { constraints: concatMap (toKimchiRows <<< _.constraint) (constraintsToArray s.constraints)
  , publicInputs: s.publicInputs
  , unionFind: (un AuxState s.aux).wireState.unionFind
  }

fromCompiledCircuit
  :: forall f g
   . CircuitGateConstructor f g
  => PrimeField f
  => Ord f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Effect (Circuit f)
fromCompiledCircuit s = do
  gd <- gateDataOf s
  unless (Array.length gd.gates == Array.length gd.constraints)
    $ throw
    $ "fromCompiledCircuit: " <> show (Array.length gd.gates) <> " gates for "
        <> show (Array.length gd.constraints)
        <> " rows"
  pure (fromGateData s gd)

-- | Assemble the `Circuit` view from a compiled state and its gate data, one
-- | gate per row (`fromCompiledCircuit` checks the counts agree).
fromGateData
  :: forall f g
   . CircuitGateConstructor f g
  => PrimeField f
  => Ord f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> { constraints :: Array (KimchiRow f)
     , gates :: Array (Gate f)
     , publicInputSize :: Int
     }
  -> Circuit f
fromGateData s gd =
  let

    contexts = piContexts <> gateContexts
      where
      piContexts = replicate (Array.length s.publicInputs) []
      gateContexts = concatMap
        (\lc -> replicate (Array.length (toKimchiRows lc.constraint :: Array (KimchiRow f))) lc.context)
        (constraintsToArray s.constraints)

    gates = Array.mapWithIndex
      ( \i (Tuple row gate) ->
          let
            gateWires = circuitGateGetWires gate
            wires = Array.mapWithIndex
              ( \j _ ->
                  let
                    w = gateWiresGetWire gateWires j
                  in
                    { row: wireGetRow w, col: wireGetCol w }
              )
              (Array.replicate 7 unit)
            variables = map (map getVariable) row.variables
            context = case Array.index contexts i of
              Just ctx -> ctx
              Nothing -> []
          in
            { kind: row.kind
            , wires
            , variables
            , coeffs: row.coeffs
            , context
            }
      )
      (Array.zip gd.constraints gd.gates)

    AuxState aux = s.aux
    cachedConstants =
      Array.sortWith (_.variable)
        $ map
            ( \(Tuple fieldVal var) ->
                { variable: getVariable var
                , varType: if Set.member var aux.wireState.internalVariables then "internal" else "external"
                , value: fieldVal
                }
            )
        $ (Map.toUnfoldable aux.wireState.cachedConstants)
  in
    { publicInputSize: gd.publicInputSize
    , gates
    , cachedConstants
    }
