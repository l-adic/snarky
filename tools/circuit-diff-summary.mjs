#!/usr/bin/env node
// Circuit diff summary: gate counts, cached constants, first difference.
// Usage: node tools/circuit-diff-summary.mjs <results-json>
// Example: node tools/circuit-diff-summary.mjs packages/pickles-circuit-diffs/circuits/results/ivp_step_circuit.json

import { readFileSync } from 'node:fs';

const path = process.argv[2];
if (!path) { console.error('Usage: node tools/circuit-diff-summary.mjs <results-json>'); process.exit(1); }

const data = JSON.parse(readFileSync(path, 'utf8'));
const ps = data.purescript, oc = data.ocaml;

// Gate counts
console.log(`Status: ${data.status}`);
console.log(`Gates: PS ${ps.gates.length}  OCaml ${oc.gates.length}`);
console.log(`Public inputs: PS ${ps.publicInputSize}  OCaml ${oc.publicInputSize}`);

// Gate type breakdown
function ct(g) { const c = {}; g.forEach(x => c[x.kind] = (c[x.kind]||0) + 1); return c; }
const pst = ct(ps.gates), oct = ct(oc.gates);
const allTypes = new Set([...Object.keys(pst), ...Object.keys(oct)]);
console.log('\nGate types:');
for (const t of [...allTypes].sort()) {
  const p = pst[t]||0, o = oct[t]||0;
  const status = p === o ? 'match' : `PS ${p} vs OC ${o} (${p > o ? '+' : ''}${p-o})`;
  console.log(`  ${t.padEnd(16)} ${status}`);
}

// Cached constants
const psCC = new Set(ps.cachedConstants.map(c => c.value));
const ocCC = new Set(oc.cachedConstants.map(c => c.value));
const shared = [...psCC].filter(v => ocCC.has(v)).length;
const psOnly = psCC.size - shared, ocOnly = ocCC.size - shared;
console.log(`\nCached constants: PS ${psCC.size}  OCaml ${ocCC.size}  shared ${shared}  PS-only ${psOnly}  OC-only ${ocOnly}`);
if (psOnly > 0) {
  console.log('  PS-only (first 3):');
  [...psCC].filter(v => !ocCC.has(v)).slice(0, 3).forEach(v => console.log(`    ${v.substring(0, 60)}...`));
}
if (ocOnly > 0) {
  console.log('  OC-only (first 3):');
  [...ocCC].filter(v => !psCC.has(v)).slice(0, 3).forEach(v => console.log(`    ${v.substring(0, 60)}...`));
}

// First difference (kind or coefficients)
for (let i = 0; i < Math.min(ps.gates.length, oc.gates.length); i++) {
  const kindMatch = ps.gates[i].kind === oc.gates[i].kind;
  const coeffMatch = JSON.stringify(ps.gates[i].coeffs||[]) === JSON.stringify(oc.gates[i].coeffs||[]);
  if (!kindMatch || !coeffMatch) {
    console.log(`\nFirst difference at row ${i}:`);
    console.log(`  PS: ${ps.gates[i].kind}${kindMatch ? '' : ' (KIND DIFF)'} ${coeffMatch ? '' : '(COEFF DIFF)'}`);
    console.log(`  OC: ${oc.gates[i].kind}`);
    console.log(`  PS ctx: ${(ps.gates[i].context||[]).join(' > ').substring(0, 100)}`);
    console.log(`  OC ctx: ${(oc.gates[i].context||[]).join(' > ').substring(0, 100)}`);
    // Show surrounding rows
    for (let j = Math.max(0, i-2); j < Math.min(i+5, ps.gates.length); j++) {
      const km = ps.gates[j].kind === oc.gates[j].kind;
      const cm = JSON.stringify(ps.gates[j].coeffs||[]) === JSON.stringify(oc.gates[j].coeffs||[]);
      const mark = (km && cm) ? '  ' : (km ? 'C!' : 'K!');
      console.log(`  ${mark} ${j} ${ps.gates[j].kind.padEnd(14)} | ${(ps.gates[j].context||[]).slice(-1)[0]?.substring(0, 40) || ''}`);
    }
    break;
  }
}
if (ps.gates.length === oc.gates.length) {
  let allMatch = true;
  for (let i = 0; i < ps.gates.length; i++) {
    if (ps.gates[i].kind !== oc.gates[i].kind || JSON.stringify(ps.gates[i].coeffs||[]) !== JSON.stringify(oc.gates[i].coeffs||[])) {
      allMatch = false; break;
    }
  }
  if (allMatch) console.log('\nAll gates match exactly (kinds + coefficients).');
}

// Section breakdown (top-2 context levels)
console.log('\nSections (by context):');
function sectionCounts(gates, label) {
  const sections = {};
  gates.forEach((g, i) => {
    const ctx = (g.context || []).slice(0, 2).join(' > ') || '(none)';
    if (!sections[ctx]) sections[ctx] = { count: 0, start: i, kinds: {} };
    sections[ctx].count++;
    sections[ctx].kinds[g.kind] = (sections[ctx].kinds[g.kind]||0) + 1;
    sections[ctx].end = i;
  });
  return sections;
}
const psSec = sectionCounts(ps.gates);
for (const [k, v] of Object.entries(psSec).sort((a, b) => a[1].start - b[1].start)) {
  console.log(`  ${v.start}-${v.end} ${k} (${v.count} gates)`);
}
