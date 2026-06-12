// Measurement harness mirroring packages/pickles-bench/src/BenchUtils.js:
// the SAME `[bench-window] start/end <uptimeMs> <label>` markers (so the
// PS suite's parse_gclog.mjs attaches GC reclaim per window unchanged)
// and the SAME bench-results JSON schema (so existing tooling can read
// both suites side by side; cross-suite tables are rendered by
// tools — never by compare.mjs's regression gate).
import { execSync } from 'node:child_process';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { PerformanceObserver } from 'node:perf_hooks';

const sh = (cmd: string): string => {
  try {
    return execSync(cmd, { encoding: 'utf8' }).trim();
  } catch {
    return '';
  }
};

const uptimeMs = () => (process.uptime() * 1000).toFixed(0);

export function windowStart(label: string): void {
  console.log(`[bench-window] start ${uptimeMs()} ${label}`);
}

export function windowEnd(label: string): void {
  console.log(`[bench-window] end ${uptimeMs()} ${label}`);
}

export interface Sample {
  iterations: number;
  ms: number;
}

export interface BenchResult {
  name: string;
  samples: Sample[];
  stats: {
    n: number;
    meanMs: number;
    stddevMs: number | null;
    minMs: number;
    maxMs: number;
  };
}

export function stats(samples: Sample[]): BenchResult['stats'] {
  const xs = samples.map((s) => s.ms);
  const n = xs.length;
  const mean = xs.reduce((a, b) => a + b, 0) / n;
  const stddev =
    n > 1 ? Math.sqrt(xs.reduce((a, x) => a + (x - mean) ** 2, 0) / (n - 1)) : null;
  return {
    n,
    meanMs: mean,
    stddevMs: stddev,
    minMs: Math.min(...xs),
    maxMs: Math.max(...xs),
  };
}

// In-process GC tracking per trial, mirroring BenchUtils.startGcTracking/
// report: a PerformanceObserver on 'gc' entries accumulates collected
// bytes between window start/end, printed in the SAME report shape the
// PS suite logs after each trial. CAVEAT: observes the MAIN isolate
// only — o1js worker-thread heaps are invisible here AND to --trace-gc.
interface GcEvent {
  collected: number;
}

let gcEvents: GcEvent[] = [];
let gcObs: PerformanceObserver | null = null;

function startGcTracking(): void {
  gcEvents = [];
  gcObs = new PerformanceObserver((list) => {
    for (const entry of list.getEntries()) {
      const detail = (entry as unknown as { detail?: { beforeGC?: number; afterGC?: number } })
        .detail ?? {};
      gcEvents.push({ collected: (detail.beforeGC ?? 0) - (detail.afterGC ?? 0) });
    }
  });
  gcObs.observe({ entryTypes: ['gc'] });
}

async function stopGcTrackingAndReport(): Promise<void> {
  // Yield once so queued observer callbacks are delivered before we
  // disconnect — the native backend's noop JS thread pool makes proving
  // synchronous, so the event loop never turns during a trial and every
  // GC entry is still pending here. (PS gets this yield for free from
  // its async napi calls.)
  await new Promise((r) => setImmediate(r));
  gcObs?.disconnect();
  const totalCollected = gcEvents.reduce((a, e) => a + e.collected, 0);
  console.log('\n--- Benchmarking Report ---');
  console.log(`Total Garbage Collected: ${(totalCollected / 1024 / 1024).toFixed(2)} MB`);
  console.log(`GC Events: ${gcEvents.length}`);
}

// One timed trial wrapped in a gc window. The label appears in both the
// console markers and the artifact, exactly like the PS suite.
export async function timedTrial(label: string, body: () => Promise<void>): Promise<Sample> {
  startGcTracking();
  windowStart(label);
  const t0 = performance.now();
  await body();
  const ms = performance.now() - t0;
  windowEnd(label);
  await stopGcTrackingAndReport();
  return { iterations: 1, ms };
}

export interface Artifact {
  date: string;
  suite: 'o1js';
  backend: 'wasm' | 'native';
  o1jsVersion: string;
  gitSha: string;
  gitDirty: boolean;
  node: string;
  nodeFlags: string[];
  powerProfile: string;
  // Side-by-side equivalence evidence: rows per method, from
  // `analyzeMethods()`. The PS suite's counterpart is the compiled
  // builder state's constraint count / domain log2.
  circuitRows: Record<string, number>;
  benches: BenchResult[];
}

export function writeArtifact(
  o1jsVersion: string,
  backend: 'wasm' | 'native',
  circuitRows: Record<string, number>,
  benches: BenchResult[]
): void {
  const out: Artifact = {
    date: new Date().toISOString(),
    suite: 'o1js',
    backend,
    o1jsVersion,
    gitSha: sh('git rev-parse HEAD') || 'unknown',
    gitDirty: sh('git status --porcelain') !== '',
    node: process.version,
    nodeFlags: process.execArgv,
    powerProfile: sh('powerprofilesctl get 2>/dev/null') || 'unknown',
    circuitRows,
    benches,
  };
  const file =
    process.env.BENCH_RESULTS_FILE ||
    path.join(
      '..',
      'bench-results',
      `o1js-${backend}-${o1jsVersion}-${out.date.replace(/[:.]/g, '-')}.json`
    );
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, JSON.stringify(out, null, 2));
  console.log('[bench-results] ' + file);
}
