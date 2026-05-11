#!/usr/bin/env node
// Phase 1 of the Pickles module reorganization workflow.
//
// Generates `analysis/pickles-inventory.md` — one section per Pickles
// module, with:
//   - LOC, body classification (facade vs real)
//   - in-package imports (with names)
//   - importers (with names + cluster tag: Step/Wrap/Prove/Compile/Sideload/Verify/Test/Other)
//   - per-binding importer profile (which clusters use each exported name)
//   - tier-consistency check
//
// Inputs:  `spago graph modules --json` (regenerated if absent), source files.
// Output:  analysis/pickles-inventory.md

const fs = require("fs");
const path = require("path");
const { execSync } = require("child_process");

const ROOT = __dirname;
const DEPS_JSON = path.join(ROOT, "deps.json");
const OUTPUT_DIR = path.join(ROOT, "analysis");
const OUTPUT = path.join(OUTPUT_DIR, "pickles-inventory.md");

// ---------- 1. Load deps.json -----------------------------------------

console.log("Generating deps.json via spago graph modules...");
execSync(`npx spago graph modules --json > ${DEPS_JSON}`, { cwd: ROOT });
const allDeps = JSON.parse(fs.readFileSync(DEPS_JSON, "utf8"));

// Pickles rows = modules in the pickles package (skip the .Internal-style
// ones if they don't exist anymore).
const pickleMods = Object.entries(allDeps)
  .filter(([, e]) => e.package === "pickles")
  .map(([m]) => m)
  .sort();

const pickleModSet = new Set(pickleMods);

// ---------- 2. Parse each source file ---------------------------------

function readModuleSource(mod) {
  const entry = allDeps[mod];
  if (!entry || !entry.path) return null;
  const abs = path.join(ROOT, entry.path);
  if (!fs.existsSync(abs)) return null;
  return fs.readFileSync(abs, "utf8");
}

// Split a string on commas at paren-depth 0.
function splitTopLevelCommas(s) {
  const out = [];
  let depth = 0;
  let cur = "";
  for (const ch of s) {
    if (ch === "(") depth++;
    else if (ch === ")") depth--;
    if (ch === "," && depth === 0) {
      out.push(cur);
      cur = "";
    } else {
      cur += ch;
    }
  }
  if (cur.trim().length > 0) out.push(cur);
  return out;
}

// Normalise an export-list / import-list entry to its base identifier.
// Examples:
//   "VerificationKey(..)" -> { name: "VerificationKey", form: "type" }
//   "module Foo.Bar"       -> { name: "Foo.Bar",        form: "module" }
//   "value"                -> { name: "value",          form: "value" }
//   "class Foo"            -> { name: "Foo",            form: "class" }
//   "type (~~>)"           -> { name: "(~~>)",          form: "type" }
function classifyExportEntry(raw) {
  const s = raw.trim();
  if (s.startsWith("module ")) {
    return { name: s.slice(7).trim(), form: "module" };
  }
  if (s.startsWith("class ")) {
    return { name: s.slice(6).trim(), form: "class" };
  }
  if (s.startsWith("type ")) {
    return { name: s.slice(5).trim(), form: "type" };
  }
  if (s.startsWith("data ")) {
    return { name: s.slice(5).trim(), form: "type" };
  }
  // strip "(..)" if present and treat as type
  const tyMatch = s.match(/^([A-Z][\w']*)\s*\(\s*\.\.\s*\)$/);
  if (tyMatch) return { name: tyMatch[1], form: "type" };
  return { name: s, form: "value" };
}

// Strip line comments (`--` to end-of-line) but leave `--` inside
// string literals or operator symbols alone. For our purposes this
// crude version is fine — export/import lists don't have strings.
function stripLineComment(s) {
  const idx = s.indexOf("--");
  return idx < 0 ? s : s.slice(0, idx);
}

// Parse a paren-delimited list, supporting multi-line by accumulating
// until depth returns to 0. Returns { list: string, endLine: number }.
function accumulateParens(lines, startLine, startCol) {
  let depth = 0;
  let acc = "";
  let started = false;
  for (let i = startLine; i < lines.length; i++) {
    const raw = i === startLine ? lines[i].slice(startCol) : lines[i];
    const line = stripLineComment(raw);
    for (const ch of line) {
      if (ch === "(") {
        if (!started) { started = true; depth = 1; continue; }
        depth++;
      } else if (ch === ")") {
        depth--;
        if (depth === 0) return { list: acc, endLine: i };
      }
      if (started && depth > 0) acc += ch;
    }
    if (started) acc += "\n";
    if (!started && i > startLine + 50) return { list: "", endLine: i }; // safety
  }
  return { list: acc, endLine: lines.length };
}

function parseSource(mod) {
  const text = readModuleSource(mod);
  if (text === null) {
    return { loc: 0, exports: null, imports: [], body_kind: "missing" };
  }
  const lines = text.split("\n");
  const loc = lines.length;

  // ---- Module header / export list ----
  let exports = null;
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^module\s+[\w.]+\s*(\(?.*)?$/);
    if (!m) continue;
    const rest = m[1] || "";
    if (rest.trim().startsWith("where")) {
      // implicit (everything exported)
      exports = null;
      break;
    }
    if (!rest.startsWith("(")) {
      // multi-line where the "(" is on the next non-comment line
      // accumulate from this line; accumulateParens will skip until "("
    }
    const parenIdx = lines[i].indexOf("(");
    if (parenIdx >= 0) {
      const { list } = accumulateParens(lines, i, parenIdx);
      exports = splitTopLevelCommas(list).map((s) => s.trim()).filter(Boolean);
    } else {
      // look for "(" on next lines
      let j = i + 1;
      while (j < lines.length && !lines[j].includes("(")) j++;
      if (j < lines.length) {
        const { list } = accumulateParens(lines, j, lines[j].indexOf("("));
        exports = splitTopLevelCommas(list).map((s) => s.trim()).filter(Boolean);
      }
    }
    break;
  }

  // ---- Imports ----
  const imports = [];
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^import\s+([\w.]+)(?:\s+as\s+\w+)?(\s|\()/);
    if (!m) continue;
    const target = m[1];
    const parenIdx = lines[i].indexOf("(", m[0].length - 1);
    if (parenIdx < 0) {
      // implicit import: take everything
      imports.push({ target, names: null });
      continue;
    }
    const { list } = accumulateParens(lines, i, parenIdx);
    const names = splitTopLevelCommas(list).map((s) => s.trim()).filter(Boolean);
    imports.push({ target, names });
  }

  // ---- Body classification ----
  let body_kind = "real";
  if (exports !== null && exports.length > 0) {
    if (exports.every((e) => e.trim().startsWith("module "))) {
      body_kind = "facade";
    }
  }

  return { loc, exports, imports, body_kind };
}

// ---------- 3. Build per-module parse cache ---------------------------

const parsed = {}; // mod -> parsed source
for (const mod of pickleMods) parsed[mod] = parseSource(mod);

// Also parse Test.Pickles.* and Pickles.* in other packages so we can
// attribute their imports.
const testMods = Object.keys(allDeps).filter((m) => m.startsWith("Test.Pickles"));
for (const mod of testMods) parsed[mod] = parseSource(mod);

// Cross-package non-test importers of pickles (e.g. examples, codegen)
const crossMods = Object.entries(allDeps)
  .filter(([m, e]) => !m.startsWith("Test.") && e.package !== "pickles" && (e.depends || []).some((d) => pickleModSet.has(d)))
  .map(([m]) => m);
for (const mod of crossMods) parsed[mod] = parseSource(mod);

// ---------- 4. Cluster classification ---------------------------------

function clusterOf(mod) {
  if (mod.startsWith("Test.")) return "Test";
  if (!mod.startsWith("Pickles.")) return "Other";
  const rest = mod.slice("Pickles.".length);
  const dot = rest.indexOf(".");
  if (dot < 0) return "Pickles"; // flat namespace, e.g. Pickles.Types
  const head = rest.slice(0, dot);
  // Lump Prove.Compile under Compile not Prove
  if (head === "Prove" && rest === "Prove.Compile") return "Compile";
  return head;
}

// ---------- 5. Invert graph: importers per module + per binding ------

// importers[mod] = [{ importer, names | null, cluster }, ...]
const importers = Object.fromEntries(pickleMods.map((m) => [m, []]));

for (const [importer, p] of Object.entries(parsed)) {
  for (const imp of p.imports) {
    if (!pickleModSet.has(imp.target)) continue;
    importers[imp.target].push({
      importer,
      names: imp.names,
      cluster: clusterOf(importer),
    });
  }
}

// For each module's binding, who imports it (by name)?
// Returns Map<bindingName, Set<importerMod>> for each module.
const bindingImporters = {};
for (const mod of pickleMods) {
  const map = new Map();
  for (const { importer, names } of importers[mod]) {
    if (names === null) {
      // Implicit: attribute all exports
      const exps = parsed[mod].exports;
      if (exps === null) continue; // can't attribute
      for (const e of exps) {
        const { name } = classifyExportEntry(e);
        if (!map.has(name)) map.set(name, new Set());
        map.get(name).add(importer);
      }
      continue;
    }
    for (const n of names) {
      const { name } = classifyExportEntry(n);
      if (!map.has(name)) map.set(name, new Set());
      map.get(name).add(importer);
    }
  }
  bindingImporters[mod] = map;
}

// ---------- 6. Tier classification -------------------------------------

// Per-importer-cluster: what's the max tier number a module imported by
// this cluster can sit at? (Lower = stricter. The cluster's own tier is
// the upper bound for things it imports.)
function clusterMaxTier(cluster) {
  switch (cluster) {
    case "Test": return 6;        // tests can import anything
    case "Compile": return 4;
    case "Prove": return 3;       // Pickles.Prove.{Step,Wrap,Pure.*}
    case "Sideload": return 3;    // cross-cutting; generally Sideload modules sit at varied tiers
    case "Wrap": return 2;        // Wrap.* lives at 2b
    case "Step": return 2;        // Step.* lives at 2a
    case "Verify": return 2;      // shared by Step/Wrap finalizers
    case "Linearization": return 1;
    case "PlonkChecks": return 1;
    case "Pickles": return 1;     // flat namespace (IPA, FtComm, Pseudo, etc.)
    default: return 6;
  }
}

// Membership rule from importer-cluster set.
function tierFromClusters(clusters) {
  if (clusters.size === 0) return { tier: "??", note: "no importers (orphan)" };
  if (clusters.size === 1 && clusters.has("Test")) return { tier: "test-only", note: "" };
  const hasStep = clusters.has("Step");
  const hasWrap = clusters.has("Wrap");
  if (hasStep && hasWrap) return { tier: "≤ 1", note: "strict-AND (Step+Wrap)" };
  if (hasStep) return { tier: "≤ 2a", note: "Step-only" };
  if (hasWrap) return { tier: "≤ 2b", note: "Wrap-only" };
  // No Step or Wrap importer — compute lowest bound from remaining clusters.
  const bounds = [...clusters].map(clusterMaxTier);
  const minBound = Math.min(...bounds);
  const tag = `≤ ${minBound}`;
  const sorted = [...clusters].sort().join(", ");
  return { tier: tag, note: `imported by ${sorted}` };
}

// Natural-tier table from the algorithm.
function naturalTier(mod) {
  const rest = mod.startsWith("Pickles.") ? mod.slice(8) : mod;
  const tableLeaves = new Set([
    "Constants", "Types", "VerificationKey", "ProofsVerified",
  ]);
  if (tableLeaves.has(rest)) return "0";
  if (rest === "Verify.Types") return "0";
  const tier1 = new Set([
    "Sponge", "Pseudo", "IPA", "FtComm", "PublicInputCommit",
    "Linearization", "PlonkChecks", "Dummy",
  ]);
  if (tier1.has(rest)) return "1";
  if (rest.startsWith("Step.")) return "2a";
  if (rest.startsWith("Wrap.")) return "2b";
  if (rest.startsWith("Prove.Pure")) return "3a";
  if (rest === "Prove.Step" || rest === "Prove.Wrap") return "3b";
  if (rest === "Prove.Compile") return "4 (mislabeled — should be Pickles.Compile)";
  if (rest.endsWith(".FFI") || rest === "Trace" || rest.startsWith("Util.")) return "LL";
  if (rest === "ProofFFI" || rest === "Linearization.FFI") return "LL";
  if (rest.startsWith("Sideload.")) return "feature (cross-cutting)";
  if (rest === "Verify") return "varies";
  return "?";
}

// Graph tier = 1 + max graph tier of in-package imports (leaves = 0).
function computeGraphTiers() {
  const tier = new Map(pickleMods.map((m) => [m, null]));
  // crude topological pass
  let changed = true;
  let passes = 0;
  while (changed && passes < 50) {
    changed = false; passes++;
    for (const mod of pickleMods) {
      if (tier.get(mod) !== null) continue;
      const deps = parsed[mod].imports.filter((i) => pickleModSet.has(i.target));
      if (deps.length === 0) { tier.set(mod, 0); changed = true; continue; }
      const depTiers = deps.map((d) => tier.get(d.target));
      if (depTiers.some((t) => t === null)) continue;
      tier.set(mod, 1 + Math.max(...depTiers));
      changed = true;
    }
  }
  return tier;
}
const graphTiers = computeGraphTiers();

// ---------- 7. Emit markdown ------------------------------------------

fs.mkdirSync(OUTPUT_DIR, { recursive: true });

const out = [];
out.push("# Pickles module inventory");
out.push("");
out.push("Auto-generated by `pickles-inventory.js`. Do not edit by hand.");
out.push("");
out.push("**Phase 1 of the reorganization workflow** — see `docs/pickles-tiering.md` for tier definitions and the move ledger.");
out.push("");

// Global summary
const facadeCount = pickleMods.filter((m) => parsed[m].body_kind === "facade").length;
const totalEdges = pickleMods.reduce(
  (s, m) => s + parsed[m].imports.filter((i) => pickleModSet.has(i.target)).length, 0,
);
const orphans = pickleMods.filter((m) => importers[m].length === 0);
out.push("## Summary");
out.push("");
out.push(`- **Modules**: ${pickleMods.length}`);
out.push(`- **In-package edges**: ${totalEdges}`);
out.push(`- **Facade modules**: ${facadeCount}`);
out.push(`- **Orphans (0 in-package importers, may include public-API surface)**: ${orphans.length}`);
out.push("");
if (orphans.length > 0) {
  out.push("Orphan modules:");
  for (const o of orphans.sort()) out.push(`- \`${o}\``);
  out.push("");
}

// Tier-inconsistency overview
out.push("## Tier-inconsistency candidates");
out.push("");
out.push("| Module | Natural | Graph | Cluster-implied | Note |");
out.push("|---|---|---|---|---|");
for (const mod of pickleMods) {
  const nat = naturalTier(mod);
  const gph = graphTiers.get(mod);
  const clusters = new Set(importers[mod].map((i) => i.cluster));
  const ct = tierFromClusters(clusters);
  // Flag if natural and cluster disagree
  let flag = "";
  if (nat === "0" && ct.tier !== "≤ 1" && ct.tier !== "≤ 2a" && ct.tier !== "≤ 2b" && ct.tier !== "test-only") flag = "??";
  if (nat === "1" && (ct.tier === "≤ 2a" || ct.tier === "≤ 2b")) flag = "demote to Step/Wrap";
  if (nat.startsWith("2a") && ct.tier === "≤ 1") flag = "promote to tier 1";
  if (nat.startsWith("2b") && ct.tier === "≤ 1") flag = "promote to tier 1";
  if (nat.startsWith("2a") && ct.tier === "≤ 2b") flag = "wrong cluster";
  if (nat.startsWith("2b") && ct.tier === "≤ 2a") flag = "wrong cluster";
  if (!flag) continue;
  out.push(`| \`${mod}\` | ${nat} | ${gph} | ${ct.tier} (${ct.note}) | ${flag} |`);
}
out.push("");

// Per-module sections
out.push("## Modules");
out.push("");

for (const mod of pickleMods) {
  const p = parsed[mod];
  out.push(`### \`${mod}\``);
  out.push("");
  out.push(`- **LOC**: ${p.loc}`);
  out.push(`- **Body**: ${p.body_kind}`);
  out.push(`- **Natural tier**: ${naturalTier(mod)}`);
  out.push(`- **Graph tier**: ${graphTiers.get(mod)}`);

  const clusters = new Set(importers[mod].map((i) => i.cluster));
  const ct = tierFromClusters(clusters);
  out.push(`- **Cluster-implied tier**: ${ct.tier}${ct.note ? ` (${ct.note})` : ""}`);
  out.push(`- **Importer cluster breakdown**: ${
    [...clusters].sort().map((c) => {
      const count = importers[mod].filter((i) => i.cluster === c).length;
      return `${c}×${count}`;
    }).join(", ") || "(none)"
  }`);
  out.push("");

  // Exports
  if (p.exports === null) {
    out.push("**Exports**: (implicit — all top-level)");
  } else {
    out.push("**Exports**:");
    for (const e of p.exports) out.push(`- \`${e}\``);
  }
  out.push("");

  // In-package imports
  const inPkgImports = p.imports.filter((i) => pickleModSet.has(i.target));
  if (inPkgImports.length === 0) {
    out.push("**In-package imports**: (none)");
  } else {
    out.push("**In-package imports**:");
    for (const imp of inPkgImports.sort((a, b) => a.target.localeCompare(b.target))) {
      const ns = imp.names === null ? "(implicit)" : imp.names.map((n) => "`" + n + "`").join(", ");
      out.push(`- \`${imp.target}\` — ${ns}`);
    }
  }
  out.push("");

  // Importers
  if (importers[mod].length === 0) {
    out.push("**Importers**: (none)");
  } else {
    out.push("**Importers** (with names):");
    for (const { importer, names, cluster } of importers[mod].sort((a, b) => a.importer.localeCompare(b.importer))) {
      const ns = names === null ? "(implicit)" : names.map((n) => "`" + n + "`").join(", ");
      out.push(`- \`${importer}\` [${cluster}] — ${ns}`);
    }
  }
  out.push("");

  // Per-binding importer profile
  const bMap = bindingImporters[mod];
  if (bMap.size > 0 && p.exports !== null) {
    out.push("**Per-binding importer clusters**:");
    for (const e of p.exports) {
      const { name } = classifyExportEntry(e);
      const set = bMap.get(name);
      if (!set || set.size === 0) {
        out.push(`- \`${name}\`: (unused or attribution failed)`);
        continue;
      }
      const cs = new Set([...set].map(clusterOf));
      const cTier = tierFromClusters(cs);
      out.push(`- \`${name}\`: ${[...cs].sort().join(", ")} → ${cTier.tier}${cTier.note ? ` (${cTier.note})` : ""}`);
    }
  }
  out.push("");
  out.push("---");
  out.push("");
}

fs.writeFileSync(OUTPUT, out.join("\n"));
console.log(`Wrote ${OUTPUT} (${pickleMods.length} modules, ${totalEdges} edges).`);
