#!/usr/bin/env node
// Wire diff: finds the first gate where wires differ between PS and OCaml.
// Only meaningful when kind+coefficients already match (Phase 2).
//
// Usage: node tools/circuit-wire-diff.mjs <results-json> [context-lines]
// Example: node tools/circuit-wire-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 5

import { readFileSync } from 'node:fs';

const path = process.argv[2];
const contextLines = parseInt(process.argv[3] || '5');
if (!path) { console.error('Usage: node tools/circuit-wire-diff.mjs <results-json> [context-lines]'); process.exit(1); }

const data = JSON.parse(readFileSync(path, 'utf8'));
const ps = data.purescript.gates, oc = data.ocaml.gates;

console.log(`Gates: PS ${ps.length}  OCaml ${oc.length}`);

if (ps.length !== oc.length) {
  console.log('WARNING: gate counts differ — wire comparison may not be meaningful until counts match.');
}

// Check kind+coeff status first
let kindCoeffDiffs = 0;
for (let i = 0; i < Math.min(ps.length, oc.length); i++) {
  if (ps[i].kind !== oc[i].kind || JSON.stringify(ps[i].coeffs || []) !== JSON.stringify(oc[i].coeffs || [])) {
    kindCoeffDiffs++;
  }
}
if (kindCoeffDiffs > 0) {
  console.log(`NOTE: ${kindCoeffDiffs} kind/coeff diffs remain. Wire diffs may be symptomatic, not root-cause.`);
}

// Find first wire diff
let firstDiff = -1;
for (let i = 0; i < Math.min(ps.length, oc.length); i++) {
  if (JSON.stringify(ps[i].wires) !== JSON.stringify(oc[i].wires)) {
    firstDiff = i;
    break;
  }
}

if (firstDiff === -1 && ps.length === oc.length) {
  console.log('All wires match exactly.');
  process.exit(0);
}

if (firstDiff === -1) {
  console.log(`Wire prefix matches for ${Math.min(ps.length, oc.length)} shared gates, but gate counts differ.`);
  process.exit(1);
}

console.log(`\nFirst wire difference at row ${firstDiff}:`);
console.log(`  PS ctx: ${(ps[firstDiff].context || []).join(' > ').substring(0, 120)}`);
console.log(`  OC ctx: ${(oc[firstDiff].context || []).join(' > ').substring(0, 120)}`);

// Show which wire columns differ
const psW = ps[firstDiff].wires || [];
const ocW = oc[firstDiff].wires || [];
for (let c = 0; c < Math.max(psW.length, ocW.length); c++) {
  const pw = psW[c], ow = ocW[c];
  const match = pw && ow && pw.row === ow.row && pw.col === ow.col;
  if (!match) {
    const pStr = pw ? `(r${pw.row},c${pw.col})` : 'missing';
    const oStr = ow ? `(r${ow.row},c${ow.col})` : 'missing';
    console.log(`  col ${c}: PS ${pStr}  OC ${oStr}`);
  }
}

// Show surrounding rows
const start = Math.max(0, firstDiff - contextLines);
const end = Math.min(Math.min(ps.length, oc.length), firstDiff + contextLines + 1);
console.log(`\n${''.padEnd(3)} ${'row'.padEnd(5)} ${'kind'.padEnd(14)} ${'wire diff cols'.padEnd(30)} context`);
console.log('-'.repeat(100));
for (let i = start; i < end; i++) {
  const wireMatch = JSON.stringify(ps[i].wires) === JSON.stringify(oc[i].wires);
  const kindMatch = ps[i].kind === oc[i].kind;
  const coeffMatch = JSON.stringify(ps[i].coeffs || []) === JSON.stringify(oc[i].coeffs || []);
  const mark = wireMatch ? '  ' : 'W!';

  // List which columns differ
  let diffCols = [];
  const pw = ps[i].wires || [], ow = oc[i].wires || [];
  for (let c = 0; c < Math.max(pw.length, ow.length); c++) {
    if (!pw[c] || !ow[c] || pw[c].row !== ow[c].row || pw[c].col !== ow[c].col) {
      diffCols.push(c);
    }
  }
  const diffStr = wireMatch ? '' : `cols[${diffCols.join(',')}]`;
  const extra = (!kindMatch ? ' K!' : '') + (!coeffMatch ? ' C!' : '');
  const ctx = (ps[i].context || []).slice(-1)[0]?.substring(0, 40) || '';
  console.log(`${mark} ${String(i).padEnd(5)} ${ps[i].kind.padEnd(14)} ${diffStr.padEnd(30)} ${ctx}${extra}`);
}

// Summary: count total wire diffs
let totalWireDiffs = 0;
for (let i = 0; i < Math.min(ps.length, oc.length); i++) {
  if (JSON.stringify(ps[i].wires) !== JSON.stringify(oc[i].wires)) totalWireDiffs++;
}
console.log(`\nTotal wire diffs: ${totalWireDiffs} / ${Math.min(ps.length, oc.length)} gates`);
