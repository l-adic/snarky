#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { execSync } = require("child_process");

// Usage: node workspace-deps.js [--exclude pkg1,pkg2]
const args = process.argv.slice(2);
const excludeIdx = args.indexOf("--exclude");
const excludePkgs = new Set(excludeIdx >= 0 ? args[excludeIdx + 1].split(",") : []);

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

const lines = ["digraph deps {", "  rankdir=TB;", "  node [shape=box, fontsize=10];", "  compound=true;", ""];

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
console.log(`${Object.keys(filtered).length} modules, ${edgeCount} edges, ${workspacePkgs.size} packages`);
