#!/usr/bin/env node
// Dead-code finder for internal PureScript modules.
//
// Reads CoreFn JSON (produced by `purs compile -g corefn`, what spago emits
// into ./output/<Module>/corefn.json), computes reachability from every
// test.main declared in `packages/*/spago.yaml`, and reports exported
// top-level value bindings that nothing reachable references.
//
// Caveats (see docstring in dead-code guide, or the commit message):
//   - Values only. CoreFn is type-erased, so data/type synonyms are not
//     tracked here. Use purs strict mode (`--pedantic-packages --strict`)
//     for unused-import detection at a per-importer granularity.
//   - Type-class instances are invisible to CoreFn's `Var`/`Constructor`
//     ref nodes (they are dispatched via constraints). Instance-only
//     bindings will not be detected as live and may show as "dead" if
//     they are never called directly; filter those out manually.
//   - FFI: foreign declarations marked `IsForeign` whose JS symbols are
//     consumed directly from external JS (rare) are invisible here.
//
// Usage: node tools/dead-code.mjs [--json]

import fs from 'node:fs';
import path from 'node:path';

const ROOT = process.cwd();
const OUTPUT_DIR = path.join(ROOT, 'output');
const PACKAGES_DIR = path.join(ROOT, 'packages');
const EMIT_JSON = process.argv.includes('--json');
const INCLUDE_ALL = process.argv.includes('--all');

// Discover every test.main module from packages/*/spago.yaml.
function findEntryPoints() {
  const entries = [];
  for (const pkg of fs.readdirSync(PACKAGES_DIR)) {
    const spagoPath = path.join(PACKAGES_DIR, pkg, 'spago.yaml');
    if (!fs.existsSync(spagoPath)) continue;
    const content = fs.readFileSync(spagoPath, 'utf8');
    // Match `main: Foo.Bar` inside the `test:` block. We look for a `test:`
    // line, then the next `main:` that follows at a deeper indentation.
    const testIdx = content.search(/^\s*test:\s*$/m);
    if (testIdx === -1) continue;
    const afterTest = content.slice(testIdx);
    const mainMatch = afterTest.match(/^\s+main:\s*([\w.]+)/m);
    if (mainMatch) entries.push({ pkg, module: mainMatch[1] });
  }
  return entries;
}

// Load every corefn.json under ./output/.
function loadModules() {
  const modules = new Map(); // moduleName (dotted) -> corefn object
  if (!fs.existsSync(OUTPUT_DIR)) {
    throw new Error(`No ./output directory. Run 'spago build' first.`);
  }
  for (const d of fs.readdirSync(OUTPUT_DIR)) {
    const corefnPath = path.join(OUTPUT_DIR, d, 'corefn.json');
    if (!fs.existsSync(corefnPath)) continue;
    try {
      const m = JSON.parse(fs.readFileSync(corefnPath, 'utf8'));
      modules.set(m.moduleName.join('.'), m);
    } catch (e) {
      // Ignore malformed files (partial builds).
    }
  }
  return modules;
}

// A module is "internal" iff its source lives under packages/ (not .spago/).
function isInternal(mod) {
  return mod.modulePath && mod.modulePath.startsWith('packages/');
}

// Walk an expression tree and yield every qualified reference
// ({ module, identifier }). Three source shapes in CoreFn:
//   * `Var`                 — qualified value reference
//   * `Constructor`         — data constructor in expression position
//   * `ConstructorBinder`   — data constructor in pattern-match position
function* findRefs(node) {
  if (!node || typeof node !== 'object') return;
  if (Array.isArray(node)) {
    for (const x of node) yield* findRefs(x);
    return;
  }
  if (node.type === 'Var' && node.value?.moduleName) {
    yield { module: node.value.moduleName.join('.'), ident: node.value.identifier };
  }
  if (node.type === 'Constructor' && node.value?.typeName?.moduleName) {
    yield {
      module: node.value.typeName.moduleName.join('.'),
      ident: node.value.identifier,
    };
  }
  if (node.binderType === 'ConstructorBinder' && node.constructorName?.moduleName) {
    yield {
      module: node.constructorName.moduleName.join('.'),
      ident: node.constructorName.identifier,
    };
  }
  for (const k in node) {
    if (k === 'sourceSpan' || k === 'annotation') continue;
    yield* findRefs(node[k]);
  }
}

// Heuristic: PureScript type-class instance bindings follow the pattern
// `<className><TypeName>` (lowercase class + uppercase type name), with
// a trailing `_` for the `Newtype` class hack. We can't see them as
// reachable via CoreFn because they are dispatched through dictionary
// resolution at call sites, not direct `Var` refs.
//
// Filter conservatively — only names that really look like instance
// bindings. If you want the raw list, pass `--all`.
const INSTANCE_PREFIXES = [
  'eq', 'ord', 'show', 'read',
  'functor', 'apply', 'applicative', 'bind', 'monad',
  'functorWithIndex', 'foldable', 'foldableWithIndex',
  'traversable', 'traversableWithIndex',
  'semigroup', 'monoid', 'semiring', 'ring', 'commutativeRing',
  'euclideanRing', 'field', 'divisionRing',
  'heytingAlgebra', 'booleanAlgebra',
  'bounded', 'boundedEnum', 'enum',
  'generic', 'newtype', 'coerce',
  'arbitrary', 'coarbitrary',
  'unfoldable', 'unfoldable1',
  'hashable',
  'decodeJson', 'encodeJson',
  'semigroupoid', 'category', 'profunctor', 'strong', 'choice',
  'alt', 'alternative', 'plus',
  'extend', 'comonad',
  'liftEq', 'liftShow', 'liftOrd',
  'nonEmpty', 'distributive',
  'eq1', 'show1', 'ord1',
  'traversableOneTypeclassConstructor',
];

function looksLikeInstance(ident) {
  if (ident.endsWith('_')) return true;
  for (const p of INSTANCE_PREFIXES) {
    if (ident === p) return true;
    if (ident.startsWith(p)) {
      const next = ident[p.length];
      if (next && next >= 'A' && next <= 'Z') return true;
    }
  }
  return false;
}

// Return a map ident → expression for every top-level bind in a module's decls.
function declMap(mod) {
  const m = new Map();
  for (const d of mod.decls) {
    if (d.bindType === 'NonRec') {
      m.set(d.identifier, d.expression);
    } else if (d.bindType === 'Rec') {
      for (const b of d.binds) m.set(b.identifier, b.expression);
    }
  }
  return m;
}

function keyOf(modName, ident) {
  return `${modName}::${ident}`;
}

function main() {
  const entries = findEntryPoints();
  const modules = loadModules();

  if (entries.length === 0) {
    console.error('No test.main entries found. Check packages/*/spago.yaml.');
    process.exit(1);
  }

  // Reachability: BFS from every entry point's `main` binding.
  const reachable = new Set(); // key = "Module::ident"
  const queue = [];

  for (const e of entries) {
    queue.push(keyOf(e.module, 'main'));
  }

  // Also mark every binding inside an entry-point module as reachable —
  // entry modules sometimes have supporting top-level defs that `main`
  // references indirectly (e.g., via as-prover closures that aren't fully
  // reconstructed in CoreFn). Keep this generous: entry modules are
  // always alive in full.
  for (const e of entries) {
    const mod = modules.get(e.module);
    if (!mod) continue;
    for (const [ident] of declMap(mod)) {
      queue.push(keyOf(e.module, ident));
    }
  }

  const declCache = new Map();
  const getDecls = (modName) => {
    if (declCache.has(modName)) return declCache.get(modName);
    const mod = modules.get(modName);
    const map = mod ? declMap(mod) : new Map();
    declCache.set(modName, map);
    return map;
  };

  while (queue.length > 0) {
    const key = queue.pop();
    if (reachable.has(key)) continue;
    reachable.add(key);

    const [modName, ident] = key.split('::');
    const decls = getDecls(modName);
    const expr = decls.get(ident);
    if (!expr) continue; // no local decl (might be a re-export, or type-only)

    for (const ref of findRefs(expr)) {
      queue.push(keyOf(ref.module, ref.ident));
    }
  }

  // Report.
  const deadByModule = new Map(); // modName -> [idents]
  let liveInternalCount = 0;
  let deadCount = 0;

  for (const [modName, mod] of modules) {
    if (!isInternal(mod)) continue;
    const decls = declMap(mod);
    const dead = [];
    for (const exp of mod.exports) {
      // Only flag things that have a local decl (skip pure re-exports).
      if (!decls.has(exp)) continue;
      if (!reachable.has(keyOf(modName, exp))) {
        if (!INCLUDE_ALL && looksLikeInstance(exp)) continue;
        dead.push(exp);
        deadCount++;
      } else {
        liveInternalCount++;
      }
    }
    if (dead.length > 0) deadByModule.set(modName, dead);
  }

  if (EMIT_JSON) {
    const obj = {};
    for (const [m, idents] of deadByModule) obj[m] = idents;
    process.stdout.write(JSON.stringify(obj, null, 2) + '\n');
    return;
  }

  // Pretty print.
  console.log(`Entry points (test.main):`);
  for (const e of entries) console.log(`  ${e.pkg}: ${e.module}`);
  console.log();
  console.log(`Scanned ${modules.size} modules (${Array.from(modules.values()).filter(isInternal).length} internal).`);
  console.log(`Reachable internal exports: ${liveInternalCount}`);
  console.log(`Dead internal exports: ${deadCount}`);
  console.log();
  if (deadCount === 0) {
    console.log('No dead exports found.');
    return;
  }
  const sorted = Array.from(deadByModule.keys()).sort();
  for (const m of sorted) {
    console.log(`${m}`);
    for (const i of deadByModule.get(m).sort()) console.log(`    ${i}`);
  }
}

main();
