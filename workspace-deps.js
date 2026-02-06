#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { execSync } = require("child_process");

// Usage: node workspace-deps.js [--exclude pkg1,pkg2] [--closure pkg]
const args = process.argv.slice(2);
const excludeIdx = args.indexOf("--exclude");
const excludePkgs = new Set(excludeIdx >= 0 ? args[excludeIdx + 1].split(",") : []);
const closureIdx = args.indexOf("--closure");
const closurePkg = closureIdx >= 0 ? args[closureIdx + 1] : null;

const ROOT = __dirname;
const DEPS_JSON = path.join(ROOT, "deps.json");
const OUTPUT_DOT = path.join(ROOT, "deps.dot");
const OUTPUT_SVG = path.join(ROOT, "deps.svg");

// Generate deps.json from spago
console.log("Generating deps.json via spago graph modules...");
execSync(`npx spago graph modules --json > ${DEPS_JSON}`, { cwd: ROOT });

// 1. Get workspace package names from packages/*/spago.yaml
const packagesDir = path.join(ROOT, "packages");
const workspacePkgs = new Set(
  fs.readdirSync(packagesDir).flatMap((dir) => {
    const yamlPath = path.join(packagesDir, dir, "spago.yaml");
    if (!fs.existsSync(yamlPath)) return [];
    const match = fs.readFileSync(yamlPath, "utf8").match(/^\s*name:\s*(.+)$/m);
    return match ? [match[1].trim()] : [];
  })
);

// 2. Filter deps.json to workspace packages only
const allDeps = JSON.parse(fs.readFileSync(DEPS_JSON, "utf8"));
const filtered = {};
for (const [mod, entry] of Object.entries(allDeps)) {
  if (workspacePkgs.has(entry.package) && !mod.startsWith("Test.") && !excludePkgs.has(entry.package)) {
    filtered[mod] = entry;
  }
}

// 3. Trim depends lists to workspace-only modules
const validModules = new Set(Object.keys(filtered));
for (const entry of Object.values(filtered)) {
  entry.depends = entry.depends.filter((dep) => validModules.has(dep));
}

// 3b. If --closure is specified, compute the transitive closure of that package's
//     dependencies and drop everything else.
if (closurePkg) {
  // Collect all modules belonging to the closure root package
  const seeds = new Set();
  for (const [mod, entry] of Object.entries(filtered)) {
    if (entry.package === closurePkg) seeds.add(mod);
  }
  if (seeds.size === 0) {
    console.error(`No modules found for package "${closurePkg}".`);
    console.error(`Available packages: ${[...new Set(Object.values(filtered).map((e) => e.package))].sort().join(", ")}`);
    process.exit(1);
  }

  // BFS over module-level depends to find all reachable modules
  const reachable = new Set(seeds);
  const queue = [...seeds];
  while (queue.length) {
    const cur = queue.shift();
    for (const dep of filtered[cur]?.depends || []) {
      if (!reachable.has(dep)) {
        reachable.add(dep);
        queue.push(dep);
      }
    }
  }

  // Remove non-reachable modules
  for (const mod of Object.keys(filtered)) {
    if (!reachable.has(mod)) delete filtered[mod];
  }
  // Re-trim depends
  const closureModules = new Set(Object.keys(filtered));
  for (const entry of Object.values(filtered)) {
    entry.depends = entry.depends.filter((dep) => closureModules.has(dep));
  }
  console.log(`Closure of "${closurePkg}": ${closureModules.size} modules across ${new Set(Object.values(filtered).map((e) => e.package)).size} packages`);
}

// 4. Transitive reduction — remove edge A->C if A->B->...->C exists
const modules = Object.keys(filtered);
const adj = new Map(modules.map((m) => [m, new Set(filtered[m].depends)]));

function reachableWithout(start, skip, target) {
  // BFS from start's other neighbours, see if target is reachable
  const queue = [];
  for (const n of adj.get(start)) {
    if (n !== skip) queue.push(n);
  }
  const visited = new Set(queue);
  while (queue.length) {
    const cur = queue.shift();
    if (cur === target) return true;
    for (const n of adj.get(cur) || []) {
      if (!visited.has(n)) {
        visited.add(n);
        queue.push(n);
      }
    }
  }
  return false;
}

// For each module, check which direct deps are also reachable transitively
const reduced = new Map();
for (const mod of modules) {
  const direct = [...(adj.get(mod) || [])];
  const keep = direct.filter((dep) => !reachableWithout(mod, dep, dep));
  reduced.set(mod, keep);
}

// 5. Generate dot file with package subgraphs
const pkgColors = [
  "#e6194b40", "#3cb44b40", "#ffe11940", "#4363d840",
  "#f5823140", "#911eb440", "#42d4f440", "#f032e640",
  "#bfef4540", "#fabed440", "#46999040", "#dcbeff40",
  "#9a632440", "#fffac840", "#80000040", "#aaffc340",
];

// Group modules by package
const byPackage = new Map();
for (const [mod, entry] of Object.entries(filtered)) {
  const pkg = entry.package;
  if (!byPackage.has(pkg)) byPackage.set(pkg, []);
  byPackage.get(pkg).push(mod);
}

const lines = [
  "digraph deps {",
  "  rankdir=TB;",
  "  node [shape=box, fontsize=10, margin=\"0.12,0.06\"];",
  "  edge [color=\"#555555\"];",
  "  compound=true;",
  "  newrank=true;",
  "  ranksep=1.2;",
  "  nodesep=0.4;",
  "",
];

let colorIdx = 0;
for (const [pkg, mods] of [...byPackage.entries()].sort()) {
  const color = pkgColors[colorIdx++ % pkgColors.length];
  lines.push(`  subgraph "cluster_${pkg}" {`);
  lines.push(`    label="${pkg}";`);
  lines.push(`    style=filled;`);
  lines.push(`    color="${color}";`);
  lines.push(`    fontsize=14;`);
  lines.push(`    fontname="bold";`);
  for (const mod of mods.sort()) {
    lines.push(`    "${mod}";`);
  }
  lines.push("  }");
  lines.push("");
}

for (const [mod, deps] of reduced) {
  for (const dep of deps) {
    lines.push(`  "${mod}" -> "${dep}";`);
  }
}

// 5b. Add package-layer rank constraints so sibling packages align horizontally.
// Layers are ordered top-to-bottom (highest-level first).
const packageLayers = [
  ["pickles", "pickles-codegen"],
  ["schnorr", "merkle-tree", "example"],
  ["random-oracle"],
  ["poseidon"],
  ["snarky-curves", "snarky-kimchi"],
  ["snarky"],
  ["curves", "vector-sized", "union-find"],
];

// For each layer, pick one representative node per present package and rank=same them.
lines.push("");
lines.push("  // Package layer alignment");
for (const layer of packageLayers) {
  const reps = [];
  for (const pkg of layer) {
    const mods = byPackage.get(pkg);
    if (mods && mods.length > 0) {
      reps.push(mods.sort()[0]); // first alphabetically as representative
    }
  }
  if (reps.length >= 2) {
    lines.push(`  { rank=same; ${reps.map((r) => `"${r}"`).join("; ")}; }`);
  }
}

// Add invisible edges between layers to enforce vertical ordering.
lines.push("");
lines.push("  // Layer ordering hints");
lines.push("  edge [style=invis, weight=100];");
const layerReps = packageLayers.map((layer) => {
  for (const pkg of layer) {
    const mods = byPackage.get(pkg);
    if (mods && mods.length > 0) return mods.sort()[0];
  }
  return null;
}).filter(Boolean);
for (let i = 0; i < layerReps.length - 1; i++) {
  lines.push(`  "${layerReps[i]}" -> "${layerReps[i + 1]}";`);
}
lines.push("  edge [style=solid, weight=1];");

lines.push("}", "");
const dot = lines.join("\n");
fs.writeFileSync(OUTPUT_DOT, dot);

// 6. Render to SVG
try {
  execSync(`dot -Tsvg ${OUTPUT_DOT} -o ${OUTPUT_SVG}`);
  console.log(`Wrote ${OUTPUT_SVG}`);
} catch {
  console.log(`Wrote ${OUTPUT_DOT} (install graphviz to render SVG)`);
}

const edgeCount = [...reduced.values()].reduce((s, deps) => s + deps.length, 0);
console.log(`${Object.keys(filtered).length} modules, ${edgeCount} edges, ${byPackage.size} packages`);
