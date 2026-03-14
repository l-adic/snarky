module CircuitDiffTable where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Pickles.CircuitDiffs.Types (CircuitComparison, ComparableCircuit, ComparableGate)
import React.Basic (JSX, ReactComponent, element, fragment)
import React.Basic.DOM as R
import React.Basic.Events (handler_)
import React.Basic.Hooks (Component, component, useState, (/\))
import React.Basic.Hooks as React
import Styles (circuitDiffStyles_)

-- | FFI: virtualized gate table (needs useVirtualizer + useReactTable hooks)
foreign import _mkGateTable :: ReactComponent GateTableProps

type GateTableProps =
  { title :: String
  , gates :: Array ComparableGate
  , diffIndices :: Array Int
  , publicInputSize :: Int
  }

s :: _
s = circuitDiffStyles_

--------------------------------------------------------------------------------
-- Data logic

type DiffSummary =
  { total :: Int
  , diffs :: Int
  , diffIndices :: Array Int
  }

computeDiff :: ComparableCircuit -> ComparableCircuit -> DiffSummary
computeDiff ps ocaml =
  let
    psGates = ps.gates
    ocamlGates = ocaml.gates
    maxLen = max (Array.length psGates) (Array.length ocamlGates)
    go i acc
      | i >= maxLen = acc
      | otherwise =
          let
            eq = case Array.index psGates i, Array.index ocamlGates i of
              Just a, Just b -> gatesEqual a b
              _, _ -> false
          in
            if eq then go (i + 1) acc
            else go (i + 1) (acc { diffs = acc.diffs + 1, diffIndices = Array.snoc acc.diffIndices i })
  in
    go 0 { total: maxLen, diffs: 0, diffIndices: [] }

gatesEqual :: ComparableGate -> ComparableGate -> Boolean
gatesEqual a b =
  a.kind == b.kind
    && a.wires == b.wires
    && a.coeffs == b.coeffs

type CachedConstantRow =
  { ps :: Maybe { variable :: Int, varType :: String, value :: String }
  , ocaml :: Maybe { variable :: Int, varType :: String, value :: String }
  , match :: Boolean
  }

computeCachedConstantRows :: ComparableCircuit -> ComparableCircuit -> Array CachedConstantRow
computeCachedConstantRows ps ocaml =
  let
    psConsts = ps.cachedConstants
    ocamlConsts = ocaml.cachedConstants
    maxLen = max (Array.length psConsts) (Array.length ocamlConsts)
  in
    Array.mapWithIndex
      ( \i _ ->
          let
            p = Array.index psConsts i
            o = Array.index ocamlConsts i
            m = case p, o of
              Just a, Just b -> a.variable == b.variable && a.varType == b.varType && a.value == b.value
              _, _ -> false
          in
            { ps: p, ocaml: o, match: m }
      )
      (Array.replicate maxLen unit)

valuesEqualAsSets :: ComparableCircuit -> ComparableCircuit -> Boolean
valuesEqualAsSets ps ocaml =
  let
    psValues = Set.fromFoldable (map _.value ps.cachedConstants)
    ocamlValues = Set.fromFoldable (map _.value ocaml.cachedConstants)
  in
    psValues == ocamlValues

--------------------------------------------------------------------------------
-- Legend

gatesLegend :: DiffSummary -> Int -> JSX
gatesLegend summary publicInputSize =
  R.div
    { className: s.legend
    , children:
        [ R.span_ [ R.text ("Gates: " <> show summary.total) ]
        , R.span { className: s.legendItem, children: [ R.span { className: s.swatchPublicInput }, R.text ("Public inputs: " <> show publicInputSize) ] }
        , R.span { className: s.legendItem, children: [ R.span { className: s.swatchDiff }, R.text ("Diffs: " <> show summary.diffs) ] }
        , R.span { className: s.legendItem, children: [ R.span { className: s.swatchPiDiff }, R.text "PI diff" ] }
        ]
    }

--------------------------------------------------------------------------------
-- Cached constants view

cachedConstantsSide :: String -> Array CachedConstantRow -> (CachedConstantRow -> Maybe { variable :: Int, varType :: String, value :: String }) -> JSX
cachedConstantsSide title rows getSide =
  R.div
    { className: s.sidePanel
    , children:
        [ R.h3 { className: s.sidePanelTitle, children: [ R.text title ] }
        , R.div
            { className: s.tableContainer
            , children:
                [ R.div
                    { className: s.tableBody
                    , children:
                        [ R.div
                            { className: s.tableHeader
                            , children:
                                [ R.div { className: s.headerCellVar, children: [ R.text "Var" ] }
                                , R.div { className: s.headerCellType, children: [ R.text "Type" ] }
                                , R.div { className: s.headerCellValue, children: [ R.text "Value" ] }
                                ]
                            }
                        , fragment (map renderRow rows)
                        ]
                    }
                ]
            }
        ]
    }
  where
  renderRow row =
    let
      entry = getSide row
    in
      R.div
        { className: if row.match then s.constRow else s.constRowDiff
        , children:
            [ R.div { className: s.cell, children: [ R.text (maybe "" (show <<< _.variable) entry) ] }
            , R.div { className: s.cell, children: [ R.text (maybe "" _.varType entry) ] }
            , R.div { className: s.cellValue, children: [ R.text (maybe "" _.value entry) ] }
            ]
        }

cachedConstantsView :: CircuitComparison -> JSX
cachedConstantsView comparison =
  let
    rows = computeCachedConstantRows comparison.purescript comparison.ocaml
    setsEqual = valuesEqualAsSets comparison.purescript comparison.ocaml
    psLen = Array.length comparison.purescript.cachedConstants
    ocamlLen = Array.length comparison.ocaml.cachedConstants
    summaryText = "Constants: PS " <> show psLen <> ", OCaml " <> show ocamlLen
      <> " | Values equal as sets: "
      <> if setsEqual then "yes" else "no"
  in
    R.div_
      [ R.div { className: s.summary, children: [ R.text summaryText ] }
      , R.div
          { className: s.sideBySide
          , children:
              [ cachedConstantsSide "PureScript" rows _.ps
              , cachedConstantsSide "OCaml" rows _.ocaml
              ]
          }
      ]

--------------------------------------------------------------------------------
-- Main component

mkCircuitDiffTable :: Component { comparison :: CircuitComparison }
mkCircuitDiffTable = component "CircuitDiffTable" \{ comparison } -> React.do
  tab /\ setTab <- useState "gates"

  let
    summary = computeDiff comparison.purescript comparison.ocaml

    tabBar =
      R.div
        { className: s.tabBar
        , children:
            [ R.div
                { className: if tab == "gates" then s.tabActive else s.tab
                , onClick: handler_ (setTab (const "gates"))
                , children: [ R.text "Gates" ]
                }
            , R.div
                { className: if tab == "constants" then s.tabActive else s.tab
                , onClick: handler_ (setTab (const "constants"))
                , children: [ R.text "Cached Constants" ]
                }
            ]
        }

    gatesView =
      R.div_
        [ gatesLegend summary comparison.purescript.publicInputSize
        , R.div
            { className: s.sideBySide
            , children:
                [ element _mkGateTable
                    { title: "PureScript"
                    , gates: comparison.purescript.gates
                    , diffIndices: summary.diffIndices
                    , publicInputSize: comparison.purescript.publicInputSize
                    }
                , element _mkGateTable
                    { title: "OCaml"
                    , gates: comparison.ocaml.gates
                    , diffIndices: summary.diffIndices
                    , publicInputSize: comparison.ocaml.publicInputSize
                    }
                ]
            }
        ]

  pure $ R.div_
    [ tabBar
    , if tab == "gates" then gatesView
      else cachedConstantsView comparison
    ]
