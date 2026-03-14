import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import {
  useReactTable,
  getCoreRowModel,
  flexRender,
} from "@tanstack/react-table";
import { useVirtualizer } from "@tanstack/react-virtual";
import * as styles from "../../src/styles/gate-table.module.css";

function formatWires(wires) {
  if (!wires) return "";
  return wires.map((w) => `(${w.row},${w.col})`).join(" ");
}

function formatCoeffs(coeffs) {
  if (!coeffs || coeffs.length === 0) return "";
  return coeffs.join(", ");
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

// Props: { title, gates, diffIndices, publicInputSize }
function GateTable({ title, gates, diffIndices, publicInputSize }) {
  const parentRef = useRef(null);
  const [expanded, setExpanded] = useState({});

  const diffSet = useMemo(() => new Set(diffIndices), [diffIndices]);

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
      (idx) =>
        expanded[idx]
          ? 28 + 16 * Math.max(gates[idx]?.context?.length || 0, 1) + 8
          : 28,
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
    { className: styles.sidePanel },
    React.createElement("h3", { className: styles.title }, title),
    React.createElement(
      "div",
      { ref: parentRef, className: styles.scrollContainer },
      React.createElement(
        "div",
        { className: styles.tableBody },
        // Header
        React.createElement(
          "div",
          { className: styles.header },
          React.createElement(
            "div",
            { className: styles.headerRowNum },
            "Row"
          ),
          ...columns.map((col) =>
            React.createElement(
              "div",
              {
                key: col.id || col.accessorKey,
                className: styles.headerCell,
                style: { flex: col.flex },
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
            const isDiff = diffSet.has(virtualRow.index);
            const isPublicInput = virtualRow.index < publicInputSize;
            const isExpanded = !!expanded[virtualRow.index];
            const gate = gates[virtualRow.index];
            const hasContext = gate?.context && gate.context.length > 0;

            const rowClass = [
              styles.virtualRow,
              isPublicInput && isDiff
                ? styles.virtualRowPiDiff
                : isPublicInput
                  ? styles.virtualRowPublicInput
                  : isDiff
                    ? styles.virtualRowDiff
                    : "",
              hasContext ? styles.virtualRowClickable : "",
            ]
              .filter(Boolean)
              .join(" ");

            return React.createElement(
              "div",
              {
                key: row.id,
                className: rowClass,
                style: { transform: `translateY(${virtualRow.start}px)` },
                onClick: hasContext
                  ? () => toggle(virtualRow.index)
                  : undefined,
              },
              // Main row
              React.createElement(
                "div",
                { className: styles.rowContent },
                React.createElement(
                  "div",
                  { className: styles.rowNum },
                  hasContext
                    ? React.createElement(
                        "span",
                        { className: styles.contextIndicator },
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
                      className: styles.dataCell,
                      style: { flex: cell.column.columnDef.flex },
                    },
                    flexRender(cell.column.columnDef.cell, cell.getContext())
                  )
                )
              ),
              // Expanded context
              isExpanded && hasContext
                ? React.createElement(
                    "div",
                    { className: styles.contextExpanded },
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

export const _mkGateTable = GateTable;
