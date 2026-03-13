import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import {
  useReactTable,
  getCoreRowModel,
  flexRender,
} from "@tanstack/react-table";
import { useVirtualizer } from "@tanstack/react-virtual";

function gatesEqual(ps, ocaml) {
  if (!ps || !ocaml) return false;
  return (
    ps.kind === ocaml.kind &&
    JSON.stringify(ps.wires) === JSON.stringify(ocaml.wires) &&
    JSON.stringify(ps.coeffs) === JSON.stringify(ocaml.coeffs)
  );
}

function formatWires(wires) {
  if (!wires) return "";
  return wires.map((w) => `(${w.row},${w.col})`).join(" ");
}

function formatCoeffs(coeffs) {
  if (!coeffs || coeffs.length === 0) return "";
  return coeffs.join(", ");
}

const DIFF_COLOR = "#f8d7da";

function formatVars(variables) {
  if (!variables || !Array.isArray(variables)) return "";
  return variables.map((v) => (v === -1 ? "_" : String(v))).join(", ");
}

const columns = [
  {
    accessorKey: "kind",
    header: "Kind",
    flex: 1,
  },
  {
    id: "wires",
    header: "Wires",
    flex: 3,
    cell: ({ row }) => formatWires(row.original.wires),
  },
  {
    id: "coeffs",
    header: "Coeffs",
    flex: 3,
    cell: ({ row }) => formatCoeffs(row.original.coeffs),
  },
];

function GateTable({ title, gates, diffMap, publicInputSize }) {
  const parentRef = useRef(null);
  const [expanded, setExpanded] = useState({});

  const toggle = useCallback((idx) => {
    setExpanded((prev) => ({ ...prev, [idx]: !prev[idx] }));
  }, []);

  const table = useReactTable({
    data: gates,
    columns,
    getCoreRowModel: getCoreRowModel(),
  });

  const rowVirtualizer = useVirtualizer({
    count: gates.length,
    getScrollElement: () => parentRef.current,
    estimateSize: useCallback(
      (idx) => (expanded[idx] ? 28 + 16 * Math.max((gates[idx]?.context?.length || 0), 1) + 8 : 28),
      [expanded, gates]
    ),
    overscan: 20,
  });

  useEffect(() => {
    rowVirtualizer.measure();
  }, [expanded, rowVirtualizer]);

  const virtualRows = rowVirtualizer.getVirtualItems();
  const tableRows = table.getRowModel().rows;

  return React.createElement(
    "div",
    { style: { flex: 1, minWidth: 0 } },
    React.createElement(
      "h3",
      { style: { margin: "0 0 8px 0", fontFamily: "sans-serif" } },
      title
    ),
    React.createElement(
      "div",
      {
        ref: parentRef,
        style: {
          height: "calc(100vh - 180px)",
          overflow: "auto",
          border: "1px solid #dee2e6",
        },
      },
      React.createElement(
        "div",
        {
          style: {
            fontFamily: "monospace",
            fontSize: "12px",
          },
        },
        // Header
        React.createElement(
          "div",
          {
            style: {
              display: "flex",
              position: "sticky",
              top: 0,
              background: "#f8f9fa",
              zIndex: 1,
              borderBottom: "2px solid #dee2e6",
              padding: "6px 0",
            },
          },
          React.createElement(
            "div",
            { style: { width: 50, flexShrink: 0, padding: "0 8px", textAlign: "right", fontWeight: "bold" } },
            "Row"
          ),
          ...columns.map((col) =>
            React.createElement(
              "div",
              {
                key: col.id || col.accessorKey,
                style: { flex: col.flex, minWidth: 0, padding: "0 8px", fontWeight: "bold" },
              },
              col.header
            )
          )
        ),
        // Body
        React.createElement(
          "div",
          {
            style: {
              height: `${rowVirtualizer.getTotalSize()}px`,
              position: "relative",
            },
          },
          ...virtualRows.map((virtualRow) => {
            const row = tableRows[virtualRow.index];
            const isDiff = diffMap[virtualRow.index];
            const isPublicInput = virtualRow.index < publicInputSize;
            const isExpanded = !!expanded[virtualRow.index];
            const gate = gates[virtualRow.index];
            const hasContext = gate?.context && gate.context.length > 0;

            return React.createElement(
              "div",
              {
                key: row.id,
                style: {
                  position: "absolute",
                  top: 0,
                  left: 0,
                  width: "100%",
                  transform: `translateY(${virtualRow.start}px)`,
                  backgroundColor: isPublicInput
                    ? "#e8f0fe"
                    : isDiff
                      ? DIFF_COLOR
                      : undefined,
                  borderBottom: "1px solid #eee",
                  cursor: hasContext ? "pointer" : "default",
                },
                onClick: hasContext ? () => toggle(virtualRow.index) : undefined,
              },
              // Main row
              React.createElement(
                "div",
                {
                  style: {
                    display: "flex",
                    height: 28,
                    alignItems: "center",
                  },
                },
                React.createElement(
                  "div",
                  {
                    style: {
                      width: 50,
                      flexShrink: 0,
                      padding: "0 8px",
                      textAlign: "right",
                      color: "#888",
                      display: "flex",
                      alignItems: "center",
                      justifyContent: "flex-end",
                      gap: "2px",
                    },
                  },
                  hasContext
                    ? React.createElement(
                        "span",
                        { style: { fontSize: "9px", color: "#5a9" } },
                        isExpanded ? "\u25BC" : "\u25B6"
                      )
                    : null,
                  virtualRow.index
                ),
                ...row.getVisibleCells().map((cell) =>
                  React.createElement(
                    "div",
                    {
                      key: cell.id,
                      style: {
                        flex: cell.column.columnDef.flex,
                        minWidth: 0,
                        padding: "0 8px",
                        overflow: "hidden",
                        textOverflow: "ellipsis",
                        whiteSpace: "nowrap",
                      },
                    },
                    flexRender(cell.column.columnDef.cell, cell.getContext())
                  )
                )
              ),
              // Expanded context
              isExpanded && hasContext
                ? React.createElement(
                    "div",
                    {
                      style: {
                        padding: "2px 8px 6px 58px",
                        color: "#555",
                        fontSize: "11px",
                        lineHeight: "16px",
                      },
                    },
                    ...gate.context.map((line, i) =>
                      React.createElement("div", { key: i }, line)
                    )
                  )
                : null
            );
          })
        )
      )
    )
  );
}

function CircuitDiffTable({ comparison }) {
  const { diffMap, summary } = useMemo(() => {
    const psGates = comparison.purescript.gates;
    const ocamlGates = comparison.ocaml.gates;
    const maxLen = Math.max(psGates.length, ocamlGates.length);

    const diffMap = {};
    let diffs = 0;

    for (let i = 0; i < maxLen; i++) {
      const eq = gatesEqual(psGates[i], ocamlGates[i]);
      diffMap[i] = !eq;
      if (!eq) diffs++;
    }

    return { diffMap, summary: { total: maxLen, diffs } };
  }, [comparison]);

  return React.createElement(
    "div",
    null,
    // Summary bar
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          gap: "16px",
          padding: "8px 0",
          fontFamily: "monospace",
          fontSize: "14px",
        },
      },
      React.createElement("span", null, `Gates: ${summary.total}`),
      ...[
        { label: "Public inputs", color: "#e8f0fe", count: comparison.purescript.publicInputSize },
        { label: "Diffs", color: DIFF_COLOR, count: summary.diffs },
      ].map(({ label, color, count }) =>
        React.createElement(
          "span",
          {
            key: label,
            style: {
              display: "inline-flex",
              alignItems: "center",
              gap: "4px",
            },
          },
          React.createElement("span", {
            style: {
              display: "inline-block",
              width: 12,
              height: 12,
              backgroundColor: color,
              border: "1px solid #aaa",
            },
          }),
          `${label}: ${count}`
        )
      )
    ),
    // Side-by-side tables
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          gap: "16px",
        },
      },
      React.createElement(GateTable, {
        title: "PureScript",
        gates: comparison.purescript.gates,
        diffMap,
        publicInputSize: comparison.purescript.publicInputSize,
      }),
      React.createElement(GateTable, {
        title: "OCaml",
        gates: comparison.ocaml.gates,
        diffMap,
        publicInputSize: comparison.ocaml.publicInputSize,
      })
    )
  );
}

export const _mkCircuitDiffTable = CircuitDiffTable;
