#!/usr/bin/env node
// R1CS generation order diff: unpacks Generic gates into individual R1CS
// constraints in generation order and finds the first divergence.
//
// Each Generic gate has 2 R1CS packed: right half (indices 5-9) was generated
// first (queued), left half (indices 0-4) was generated second (new/paired).
//
// Usage: node tools/circuit-r1cs-diff.mjs <results-json> [context-lines]
// Example: node tools/circuit-r1cs-diff.mjs packages/pickles-circuit-diffs/circuits/results/ivp_step_circuit.json 8

import { readFileSync } from 'node:fs';

const path = process.argv[2];
const contextLines = parseInt(process.argv[3] || '8');
if (!path) { console.error('Usage: node tools/circuit-r1cs-diff.mjs <results-json> [context-lines]'); process.exit(1); }

const data = JSON.parse(readFileSync(path, 'utf8'));
const ps = data.purescript.gates, oc = data.ocaml.gates;

// Extract R1CS in generation order from Generic gates
function extractR1CS(gates) {
  const r1cs = [];
  for (let row = 0; row < gates.length; row++) {
    const g = gates[row];
    if (g.kind !== 'Generic') continue;
    const c = g.coeffs || [];
    if (c.length < 10) continue;
    const right = c.slice(5);  // queued = first generated
    const left = c.slice(0, 5); // new = second generated
    const isZero = arr => arr.every(v => v === '0');
    const ctx = (g.context || []).join(' > ');
    const shortCtx = (g.context || []).slice(-1)[0] || '';
    if (!isZero(right)) r1cs.push({ coeffs: right, half: 'R', row, ctx, shortCtx });
    if (!isZero(left)) r1cs.push({ coeffs: left, half: 'L', row, ctx, shortCtx });
  }
  return r1cs;
}

const psR = extractR1CS(ps);
const ocR = extractR1CS(oc);
console.log(`Total R1CS: PS ${psR.length}  OCaml ${ocR.length}`);

// Find first diff
let firstDiff = -1;
for (let i = 0; i < Math.min(psR.length, ocR.length); i++) {
  if (JSON.stringify(psR[i].coeffs) !== JSON.stringify(ocR[i].coeffs)) {
    firstDiff = i;
    break;
  }
}

if (firstDiff === -1 && psR.length === ocR.length) {
  console.log('All R1CS match in generation order.');
  process.exit(0);
}

if (firstDiff === -1) {
  console.log(`R1CS counts differ (PS ${psR.length} vs OC ${ocR.length}) but shared prefix matches.`);
  process.exit(1);
}

console.log(`\nFirst R1CS divergence at index ${firstDiff} (PS row ${psR[firstDiff].row}, OC row ${ocR[firstDiff].row}):`);

// Decode R1CS coefficients
function decodeR1CS(coeffs) {
  const [cl, cr, co, m, c] = coeffs;
  const parts = [];
  if (cl !== '0') parts.push(`${cl}*vl`);
  if (cr !== '0') parts.push(`${cr}*vr`);
  if (co !== '0') parts.push(`${co}*vo`);
  if (m !== '0') parts.push(`${m}*vl*vr`);
  if (c !== '0') parts.push(`c=${c.substring(0, 20)}${c.length > 20 ? '...' : ''}`);
  return parts.join(' + ') || '0';
}

// Show context around divergence
const start = Math.max(0, firstDiff - contextLines);
const end = Math.min(Math.min(psR.length, ocR.length), firstDiff + contextLines + 1);

console.log(`\n${'idx'.padEnd(5)} ${'PS'.padEnd(6)} ${'half'.padEnd(4)} ${'PS R1CS'.padEnd(45)} | ${'OC'.padEnd(6)} ${'half'.padEnd(4)} ${'OC R1CS'.padEnd(45)} match`);
console.log('-'.repeat(130));
for (let i = start; i < end; i++) {
  const p = psR[i], o = ocR[i];
  const match = JSON.stringify(p?.coeffs) === JSON.stringify(o?.coeffs) ? '  ' : '**';
  const pDesc = p ? decodeR1CS(p.coeffs).substring(0, 44).padEnd(45) : ''.padEnd(45);
  const oDesc = o ? decodeR1CS(o.coeffs).substring(0, 44).padEnd(45) : ''.padEnd(45);
  const pRow = p ? ('r' + p.row).padEnd(6) : ''.padEnd(6);
  const oRow = o ? ('r' + o.row).padEnd(6) : ''.padEnd(6);
  const pH = p ? p.half.padEnd(4) : ''.padEnd(4);
  const oH = o ? o.half.padEnd(4) : ''.padEnd(4);
  console.log(`${match} ${String(i).padEnd(4)} ${pRow} ${pH} ${pDesc} | ${oRow} ${oH} ${oDesc}`);
}

// Show context labels at divergence
console.log(`\nContext at divergence:`);
console.log(`  PS: ${psR[firstDiff].ctx.substring(0, 120)}`);
console.log(`  OC: ${ocR[firstDiff].ctx.substring(0, 120)}`);

// Check if a specific constant value appears — useful for tracing seal operations
const ocDivCoeffs = ocR[firstDiff].coeffs;
const targetConst = ocDivCoeffs[4] !== '0' ? ocDivCoeffs[4] : null;
if (targetConst) {
  console.log(`\nOCaml divergent R1CS has constant: ${targetConst.substring(0, 40)}...`);
  console.log('Searching for this constant in cached constants...');
  const match = data.ocaml.cachedConstants.find(c => c.value === targetConst || c.value === '-' + targetConst);
  if (match) console.log(`  Found: varType=${match.varType}`);
  else console.log('  Not found in cached constants.');
}
