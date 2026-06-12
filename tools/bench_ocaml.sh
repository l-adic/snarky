#!/usr/bin/env bash
#
# OCaml counterpart of tools/bench.sh: builds and runs the reference
# pickles bench (mina/src/lib/crypto/pickles/bench_tree/ — the same
# NRR + N=2 tree workload as the PS and o1js suites, taken from
# test_no_sideloaded.ml) and records a results artifact in
# bench-results/ with the SAME bench labels, so cross-suite tables can
# read all three side by side.
#
# Measurement contract (mirrors the PS suite):
#   - URS/lagrange + first key generation: untimed warmup compile
#   - timed compile trials INCLUDE Cache_handle.generate_or_load
#     (pickles keypairs are lazy)
#   - NRR + b0 untimed; only the b1 proves are timed
#
# No GC/FFI instrumentation here (no node runtime) — wall times only.
#
#   tools/bench_ocaml.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG="$REPO_ROOT/prof/ocaml-bench-run.log"
EXE=src/lib/crypto/pickles/bench_tree/bench_tree.exe

mkdir -p "$REPO_ROOT/prof" "$REPO_ROOT/bench-results"

echo "==> Building bench_tree (mina dev shell) ..."
( cd "$REPO_ROOT" && nix develop mina#default -c bash -c "cd mina && dune build $EXE" )

echo "==> Running (log: prof/ocaml-bench-run.log) ..."
# Deterministic seed is required by the in-tree kimchi-stubs. Do NOT set
# PICKLES_TRACE_FILE / KIMCHI_WITNESS_DUMP — their I/O would pollute the
# timings.
( cd "$REPO_ROOT" && nix develop mina#default -c bash -c \
    "cd mina && KIMCHI_DETERMINISTIC_SEED=42 ./_build/default/$EXE" ) | tee "$LOG"

MINA_SHA=$(git -C "$REPO_ROOT/mina" rev-parse --short HEAD)

node - "$LOG" "$REPO_ROOT/bench-results" "$MINA_SHA" <<'EOF'
const fs = require("fs");
const [log, outDir, minaSha] = process.argv.slice(2);
const lines = fs.readFileSync(log, "utf8").split("\n");
const grab = (re) =>
  lines
    .map((l) => l.match(re))
    .filter(Boolean)
    .map((m) => ({ iterations: 1, ms: parseFloat(m[1]) * 1000 }));
const stats = (samples) => {
  const xs = samples.map((s) => s.ms);
  const mean = xs.reduce((a, b) => a + b, 0) / xs.length;
  return {
    n: xs.length,
    meanMs: mean,
    stddevMs:
      xs.length > 1
        ? Math.sqrt(xs.reduce((a, x) => a + (x - mean) ** 2, 0) / (xs.length - 1))
        : null,
    minMs: Math.min(...xs),
    maxMs: Math.max(...xs),
  };
};
const compile = grab(/\[bench\] compile trial \d+\/\d+: ([\d.]+)s/);
const prove = grab(/\[bench\] b1 prove trial \d+\/\d+: ([\d.]+)s/);
if (!compile.length || !prove.length) {
  console.error("[bench-results] FAILED: no trial lines found in " + log);
  process.exit(1);
}
if (!lines.some((l) => l.includes("b1 verified OK"))) {
  console.error("[bench-results] FAILED: missing verify gate");
  process.exit(1);
}
const date = new Date().toISOString();
const out = {
  date,
  suite: "ocaml",
  minaCommit: minaSha,
  benches: [
    { name: "NRR + tree compile (shared warm SRS)", samples: compile, stats: stats(compile) },
    { name: "b1 recursive prove (shared warm SRS)", samples: prove, stats: stats(prove) },
  ],
};
const file = `${outDir}/ocaml-${minaSha}-${date.replace(/[:.]/g, "-")}.json`;
fs.writeFileSync(file, JSON.stringify(out, null, 2));
console.log("[bench-results] " + file);
EOF
