# Plan: an SRS cache manager (skip the redundant Lagrange-basis FFTs)

## Goal

The coordinator builds the transaction-snark SRS **twice** — once in the engine
(`p2p-worker.js`'s wasm instance) and once in the nested self-prover (`prover.js`)
— and the dominant cost is the Lagrange-basis FFTs (`addLagrangeBasis` over domains
13 / 14 / 15 in `Snarky.Example.Env.mkConfig`). Every fresh page load / Node run
pays it again.

Introduce an **SRS cache manager**: per `(curve, size, domain)`, build the Lagrange
basis with an FFT **only if it isn't already cached**; otherwise load the cached
bytes and inject them. Backed by IndexedDB in the browser and the filesystem in
Node, so the FFTs run once per machine and are skipped on every subsequent run —
and, because IndexedDB is shared same-origin, the engine and self-prover share one
cache instead of each rebuilding.

Target: the self-prover's ~40 s SRS rebuild (and every warm run's SRS build) drops
to a near-instant inject. No FFT, no memory contention.

## Why not just compile concurrently? (rejected, measured)

The engine's `mkEnv` (SRS build + compile) is a **synchronous, thread-blocking**
wasm call on the coordinator's JS thread, so the self-prover's `init` can't even be
posted until the engine releases the thread — the compiles serialize via the event
loop regardless of any "eager" flag. Forcing true overlap (posting `init` before
the engine compiles) ballooned the engine compile to **>250 s**, because two
concurrent SRS builds contend on **memory bandwidth** (the FFTs are memory-bound),
not idle CPU cores. So "spare cores" doesn't buy spare bandwidth. The eager
experiment was implemented and reverted (clean at commit `2c74ab51`). Removing the
duplicated FFT — this plan — is the actual win; injecting a precomputed basis is a
cheap, non-contending memcpy.

## Why naive SRS serde doesn't carry the bases

`SRS::lagrange_bases` is `#[serde(skip)]` — `srs.serialize()` carries the generators
(`g`, `h`) but **not** the bases (they're treated as a derived cache). A receiver
would deserialize and then FFT-rebuild on first use, so the bases must be moved
**out of band**. Proven recipe (used to bake the wrap Lagrange basis into the SP1
guest verifier, where it was ~91 % of verify time):

- `SRS::lagrange_bases()` is a **public accessor** (the field is private) → read the
  bases out.
- `poly_commitment::SRS::get_lagrange_basis_from_domain_size(n)` returns the basis
  (`Vec<PolyComm<G>>`) for a domain of size `n`.
- Re-inject via the cache: `HashMapCache::set_once(n, basis)`
  (no_std variant: `Rc<RefCell<HashMap>>::borrow_mut().insert(n, Rc::new(basis))`).

> Confirm the pinned proof-systems version exposes `lagrange_bases()` /
> `get_lagrange_basis_from_domain_size` / `HashMapCache::set_once` — present on the
> SP1 branch; adapt if the project's pin differs.

## Architecture

Two layers, mirroring the P2P `Transport` split (abstract interface in the lib,
concrete impls in the app). The platform-specific surface is **only byte
persistence**; all SRS knowledge lives in the lib, written once and tested in Node.

```
┌─ lib (browser-free, node-safe) ─────────────────────────────────┐
│  SrsCache  — platform interface: get / put bytes by SrsEntry      │
│  ensure*   — the manager: FFT-on-miss orchestration (lives once)  │  → kimchi bindings
└──────────────────────────────────────────────────────────────────┘
        ▲ implements                    ▲ implements
┌─ app/node ─────────┐         ┌─ app/web ──────────────┐
│  fsCache (Node.FS) │         │  idbCache (IndexedDB)  │
└────────────────────┘         └────────────────────────┘
```

The FFT must not be duplicated per platform, so it lives in the lib manager; the
platform implements only `get`/`put` of bytes. (FS and IndexedDB can only store
bytes anyway.)

## Backend bindings (kimchi-napi)

Per-domain, matching the existing `caml_f{p,q}_srs_add_lagrange_basis`:

```rust
// extract one domain's basis (built via add_lagrange_basis)
pub fn caml_fp_srs_lagrange_basis_to_bytes(srs: &SrsFp, log2_size: u32) -> Vec<u8> {
    let basis = srs.get_lagrange_basis_from_domain_size(1 << log2_size);
    let mut out = vec![];
    basis.serialize_compressed(&mut out).unwrap();   // arkworks CanonicalSerialize
    out
}

// inject one domain's basis into an srs (generators already present)
pub fn caml_fp_srs_set_lagrange_basis(srs: &SrsFp, log2_size: u32, bytes: &[u8]) {
    let basis: Vec<PolyComm<Vesta>> =
        CanonicalDeserialize::deserialize_compressed(bytes).unwrap();
    srs.lagrange_bases().set_once(1 << log2_size, basis);
}

// generators serde (default Serialize already skips the bases — exactly what we want)
pub fn caml_fp_srs_to_bytes(srs: &SrsFp) -> Vec<u8> { /* serialize generators */ }
pub fn caml_fp_srs_of_bytes(bytes: &[u8]) -> SrsFp  { /* deserialize generators */ }

// + caml_fq_* for Pallas
```

Exposed in both the native (napi) and wasm32-wasip1-threads builds, following the
existing `caml_*_srs_*` pattern. `Vec<u8>` marshals to `Uint8Array` on wasm (already
done for other binary returns).

## PureScript — the cache manager (lib)

```purescript
-- Snarky.Example.Srs.Cache  (browser-free, node-safe; uses the kimchi bindings)

-- What a single cache entry addresses. The platform renders it to a file path /
-- IndexedDB key. Chain-independent: the SRS is a property of the proving system.
data SrsEntry
  = Generators Curve Int        -- curve, size
  | Basis      Curve Int Int    -- curve, size, domain log2

-- The ONLY thing a platform must provide. Async to admit IndexedDB.
type SrsCache =
  { get :: SrsEntry -> Aff (Maybe ArrayBuffer)
  , put :: SrsEntry -> ArrayBuffer -> Aff Unit }

nullCache   :: SrsCache          -- never persists (lib default / safe fallback)
memoryCache :: Effect SrsCache   -- Ref of Map, for Node tests

-- The manager. FFT-on-miss lives here, once.
ensureGenerators :: SrsCache -> Curve -> Int -> Aff Srs
--   hit  → caml_*_srs_of_bytes;  miss → caml_*_srs_create(size) → put
ensureBasis :: SrsCache -> Srs -> Curve -> Int -> Int -> Aff Unit
--   hit  → set_lagrange_basis (inject, NO FFT)
--   miss → add_lagrange_basis (FFT) → lagrange_basis_to_bytes → put  (already injected)
ensureSrs :: SrsCache -> Aff SrsBundle
--   ensureGenerators "vesta" 65536 → ensureBasis 13 → ensureBasis 15
--   ensureGenerators "pallas" 32768 → ensureBasis 14
```

`Env.mkConfig`'s current `create + addLagrangeBasis [13,15] / [14]` becomes an
`ensureSrs` call; the rest of the config is assembled around the warmed
`SrsBundle` as today. With `nullCache`, behaviour is identical to the current FFT
path (no regression).

## App backends (thin — implement `SrsCache` only)

```purescript
-- app/node:  Node.FS.Aff read/write under a dir, Buffer↔ArrayBuffer
fsCache :: FilePath -> SrsCache

-- app/web:   small JS FFI over indexedDB.open + objectStore get/put (stores
--            ArrayBuffer natively; worker-accessible; shared same-origin)
idbCache :: String -> Aff SrsCache
```

The engine worker and the self-prover worker each open their own handle to the
**same** IndexedDB; the warm cache is the cross-worker channel — so this subsumes
any postMessage transfer of the bases. Remote peers each warm their own machine's
cache on first proof.

## Consistency & invalidation

- The `SrsEntry` *is* the key, so `(curve, size, domain)` changes are automatically
  a cache miss — no version field to remember to bump (add a leading format token,
  e.g. `"v1"`, only to invalidate if the byte format itself changes).
- `caml_*_srs_create(size)` is **deterministic**, so a freshly-created generator
  set is always consistent with cached bases built from the same size. Caching the
  generators is therefore a perf choice (skip `create`), not a correctness one.

## Validation

- **Round-trip unit test** (snarky-kimchi, load-bearing): build SRS →
  `lagrange_basis_to_bytes` → fresh SRS (`create`) → `set_lagrange_basis` → prove +
  verify a small circuit; assert it verifies and the commitments / VK are
  byte-identical to the FFT path.
- **Generator determinism**: `create(size)` twice → identical `g`/`h`; and
  `of_bytes(to_bytes(srs))` ≡ `srs`.
- **Manager**: against `memoryCache` in Node — first `ensureSrs` builds + stores,
  second is a pure cache hit (assert no FFT via a build counter).
- **Fallback**: `nullCache` ≡ current behaviour.
- **End-to-end**: headless coordinator — warm-run `[self] building SRS…` drops from
  ~40 s to ~instant; total startup down ~25–30 %.

## Risks

- **proof-systems API drift** — accessor / cache names must match the pinned
  version (verify first).
- **Serde format** — arkworks `CanonicalSerialize` (compressed) round-trips; pin
  compressed-vs-uncompressed + version (covered by the leading format token).
- **Cold-start double-FFT** — if engine + self both cold-miss simultaneously they
  each FFT once, then the cache is warm forever. The existing deferred ordering
  (self starts after the engine) already staggers them; accepted, no build-lock.
- **wasm `Vec<u8>` ↔ `Uint8Array`** — confirm the kimchi-napi wasm build marshals
  bytes (it already does for other binary returns).

## Scope

**In:** the per-domain + generator bindings; the lib `SrsCache` interface +
`ensure*` manager + `nullCache`/`memoryCache`; `fsCache` (node) and `idbCache`
(web); `mkConfig` refactor to `ensureSrs`; the round-trip + manager tests.

**Out (separate follow-ups):** sharing the compiled prover/verifier **index** (the
`Compiling TxCircuit…` ~20 s — bigger serde); a build-time prebuilt-basis **asset**
(removes even the first-ever FFT); eviction policy.

## Phased plan

1. **De-risk the core** (load-bearing): the kimchi-napi bindings + the snarky-kimchi
   round-trip test (build → to_bytes → fresh SRS → set → prove+verify byte-identical).
   Proves the serde-skip workaround end-to-end before any app wiring.
2. **Lib manager**: `SrsEntry` / `SrsCache` / `ensure*` / `nullCache` / `memoryCache`;
   refactor `mkConfig`'s SRS build to `ensureSrs`; Node manager test (FFT-once).
3. **App backends + wiring**: `fsCache`, `idbCache`; pass the cache into the engine
   and self-prover (`buildProver`); validate the warm-run startup drop headlessly.

## Estimated payoff

- **Per machine:** the SRS Lagrange-basis FFTs run once, ever (per `(curve,size,
  domain)`); every subsequent run — including the coordinator's self-prover, which
  shares the engine's same-origin cache — skips them.
- **Coordinator startup:** ~30–40 s off the warm path (the self-prover's FFT), zero
  contention risk.
