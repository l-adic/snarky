// TypeScript contract for the shared bench runner. The o1js suite imports
// `bench-harness` typed by this file; the PureScript suite binds the same module
// via an FFI module (`Bench.Harness`). Both resolve the identical index.js.

/** One workload. `prepare` is untimed (run once); `work` is the timed unit. */
export interface Group {
  label: string;
  trials: number;
  /** Untimed setup, run once before the group's trials (= benchlib prepareInput). */
  prepare: () => Promise<void>;
  /** The one timed unit, run `trials` times. */
  work: () => Promise<void>;
}

/** Optional per-trial site instrumentation around the timed region. */
export interface Hooks {
  onStart?: (label: string) => void;
  onEnd?: (label: string) => void;
}

export interface Sample {
  iterations: number;
  ms: number;
}

export interface Stats {
  n: number;
  meanMs: number | null;
  stddevMs: number | null;
  minMs: number | null;
  maxMs: number | null;
}

/** What `runBench` returns; sites may add fields (e.g. PS `ffi`) before writing. */
export interface Bench {
  name: string;
  samples: Sample[];
  stats: Stats;
  [extra: string]: unknown;
}

/** Run every group's trials and return the collected benches. */
export function runBench(groups: Group[], hooks?: Hooks): Promise<Bench[]>;

/** Write the run artifact. `payload` carries `suite` + `benches` + site extras. */
export function writeArtifact(payload: {
  suite: string;
  benches: Bench[];
  backend?: string;
  [extra: string]: unknown;
}): void;

export function windowStart(label: string): void;
export function windowEnd(label: string): void;
export function forceGc(): void;
export function stats(samples: Sample[]): Stats;
