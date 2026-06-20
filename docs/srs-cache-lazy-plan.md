# Lazy, persistent Lagrange-basis caching — threading the cache through compile + prove

> **Final shape (post-implementation).** What started as an "SRS cache" became a
> **Lagrange-basis cache** — the package is `lagrange-cache` (`Snarky.Lagrange.*`).
> The SRS *generators* are cheap, deterministic, and always built by the caller;
> only the expensive Lagrange bases are persisted. The cache is **sync-only**
> (`LagrangeCache`, `Effect` get/put) — the async interface existed only to load
> generators, now gone; the browser IndexedDB backend adapts via hydrate/flush.
> A basis is keyed by an **SRS fingerprint** (`blake2b` of the serialized
> generators), not `(curve, size)`, so two different SRSes for the same curve
> never collide. The sections below describe the original compile-threading
> design, which all still holds.

## Goal

Stop guessing which Lagrange-basis domains to warm. Today `Env.mkConfig`, the
pickles `SharedSrs`, and the bench `mkBenchSrs` each pre-warm a hand-picked set
of domains (`[13,15]`, `[9..16]`, …) into the SRS before compiling. That is both
**wasteful** (cold FFTs for domains a program never commits over) and **fragile**
(a circuit change silently needs a domain nobody warmed → a slow in-process FFT
that is never persisted).

Replace it with: **the SRS carries only its generators; every Lagrange basis is
materialized on first real demand, at the exact domain the circuit uses, routed
through the on-disk cache so it is computed once ever and injected from disk
forever after.** No domain lists anywhere.

## Why a compile-time seam is sufficient (the key insight)

Walking the two paths (see the exploration notes), every place a Lagrange basis
is *materialized* sits at a domain that is **fixed at compile time**:

| When | Site (curve @ domain) | What it does |
| --- | --- | --- |
| compile | pallas @ `slotWrapDomainLog2` — `shapeCompileData` (`Compile.purs`), `mkConstLagrangeBaseLookup` over `srsLagrangeCommitmentChunksAt pallasSrs …` | bakes the wrap-VK Lagrange commitments the step circuit verifies |
| compile | vesta @ `stepDomainLog2` — `buildWrapMainConfigMulti` (`Wrap.purs`), `srsLagrangeCommitmentChunksAt vestaSrs …` | bakes the step-side commitments the wrap circuit verifies |
| prove | step circuit's own domain — kimchi `pallasCreateProofWithPrev`/`vestaCreateProofWithPrev` internal `get_lagrange_basis` | witness / public-input commitment |
| prove | wrap circuit's own domain — same | witness / public-input commitment |

The domain of every circuit is pinned at compile: step via
`preComputeStepDomainLog2` / `proverIndexDomainLog2`, wrap via
`wrapDomainLog2ForProofsVerified(mpvMax)` (13/14/15 for N=0/1/2) or
`wrapDomainOverride`. Crucially, **the union of the compile-time *read* domains
equals the union of all circuits' prover-index domains**, which equals the set of
prove-time demands — because the only domains a wrap circuit reads are the step
domains it verifies, and the only domains a slot reads are the wrap-VK domains it
verifies, and each of those is some circuit's own domain inside the same
`compileMulti`.

⇒ If we warm the program's domains (step domains on vesta, wrap domain on pallas)
at compile, the **same `CRS` object is shared by reference between compile and
every prove in the process** (a prover is always constructed by compiling — there
is no other way to get one). So a basis warmed at compile is (1) already in
kimchi's in-Rust SRS cache for prove to reuse with no recompute, and (2)
persisted to disk by our cache for the next run. Best of both — and **prove needs
no cache seam at all.** This is a **compile-only** design.

## Design

### 1. Thread an optional sync cache through the configs

The cache is `Snarky.Srs.Cache.Sync.SrsCacheSync` (Effect-based) — compile is
`Effect` and the kimchi ops are `Effect`, so the sync cache keeps everything in
one non-yielding context (same reason the test/bench consumers use it).

```purescript
-- Pickles.Prove.Compile
type CompileMultiConfig =
  { srs :: { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  , lagrangeCache :: Maybe SrsCacheSync   -- NEW; Nothing = today's kimchi-lazy, no persistence
  , wrapDomainOverride :: Maybe Int
  , proofCache :: Maybe ProofCache
  , …
  }
```

`compileTxCircuit` (example) gains the same field and forwards it.

`ensureBasisSync` already exists and does what we need: cache hit →
`setBasisFromBytes` (inject, no FFT); miss → `addBasis` (FFT, which also populates
the in-`CRS` cache) + serialize + store. Either way the in-process `CRS` ends up
holding the basis, so the subsequent lazy `srsLagrangeCommitmentChunksAt` read
(compile) and kimchi `get_lagrange_basis` (prove) are both hits.

### 2. One warm point (verified)

The lagrange-reading closures (`mkConstLagrangeBaseLookup` in `shapeCompileData`
and `buildWrapMainConfigMulti`) are **pure** record-builders, so we don't warm
*inside* them. Instead there is a single `Effect` seam in the compile driver
`runMultiCompileFull` (`Compile.purs:2748`):

```purescript
runMultiCompileFull handler cfg rules = do
  log2s <- prePassDomainLog2s …      -- ← the REAL step domains, per branch
  -- ◀── WARM HERE (Effect; before any constraint building) ──▶
  for_ cfg.lagrangeCache \cache -> do
    let vSize = crsSize cfg.srs.vestaSrs
        pSize = crsSize cfg.srs.pallasSrs
        wrapLog2 = fromMaybe (Dummy.wrapDomainLog2ForProofsVerified mpvMax)
                             cfg.wrapDomainOverride
    for_ (Vector.toArray log2s) \d ->
      ensureBasisSync cache vestaOps cfg.srs.vestaSrs vSize d    -- step domains
    ensureBasisSync cache pallasOps cfg.srs.pallasSrs pSize wrapLog2  -- wrap domain
    -- + External slots' wrap domains / SideLoaded {13,14,15} when present (below)
  stepResults <- runMultiCompile …   -- constraint building fires the lazy closures → all hits
```

Why this point is correct:
- `prePassDomainLog2s` has already produced `log2s` — the exact step domains the
  branches commit over (no guessing). The wrap domain is `mpvMax`/`wrapDomainOverride`.
- It is **before** `runMultiCompile`, i.e. before any `mkConstLagrangeBaseLookup`
  closure fires and before `createProverIndex`, so every later read/commit is a
  warmed-`CRS` hit.
- `vesta @ {step domains}` covers both the step prover indices' own domains and the
  `buildWrapMainConfigMulti` step-side reads; `pallas @ wrap domain` covers the
  wrap prover index and the Self-slot wrap-VK reads.

**External / SideLoaded slots** read additional pallas domains (an imported VK's
`wrapDomainLog2`, or the full `{13,14,15}` for runtime dispatch). Those are
enumerable from the slot config at the same point; warm them in the same `for_`.
For the common self-recursive programs (all `Self` slots) the set is just
`{vesta step domains} ∪ {pallas wrap domain}`.

### 3. No prove seam

Compile-only. Because every prover is built by compiling and shares the compiled
`CRS` by reference, the bases warmed at compile are already live in kimchi's
in-process cache at prove time. Nothing to add in `stepSolveAndProve` /
`wrapSolveAndProve`.

### 4. Build the SRS with generators only

`Env.mkConfig`, `SharedSrs`, and `mkBenchSrs` stop calling `ensureSrs … domains`
and call only `ensureGenerators` (or `ensureGeneratorsSync`) per curve. All the
domain lists (`vestaDomains`, `pallasDomains`, the `[9..16]`/`[12..15]` ranges,
the bench `[13..16]`) are deleted. They pass the `lagrangeCache` into
`compile*`/`mkEnv` instead.

## Migration

1. `srs-cache`: `ensureBasisSync` already exists; nothing new needed there (the
   warm uses it directly with the domain from `prePassDomainLog2s` / wrap config).
2. `Pickles.Prove.Compile`: add `lagrangeCache :: Maybe SrsCacheSync` to
   `CompileMultiConfig`; warm in `runMultiCompileFull` right after
   `prePassDomainLog2s` (the single seam above). Pure builders untouched. No prove
   changes.
3. `example`: `compileTxCircuit`/`Env` forward `lagrangeCache`; `mkConfig` builds
   generators-only (`ensureGenerators`) and passes the cache through; drop
   `vestaDomains`/`pallasDomains`.
4. `SharedSrs`, `mkBenchSrs`: generators-only + pass cache into compile; drop the
   `[9..16]`/`[12..15]`/`[13..16]` ranges.
5. The on-disk cache dir stays `defaultSrsCacheDir` (shared across suites/runs).

## Decisions (settled)

- **Compile-only, no prove seam.** A prover is always built by compiling and
  shares the compiled `CRS`; compile-time warming covers prove (in-Rust hit) and
  persists (disk). No `stepSolveAndProve`/`wrapSolveAndProve` changes.
- **Opt-in.** `lagrangeCache :: Maybe SrsCacheSync`; default `Nothing` =
  unchanged behavior (kimchi-lazy, no persistence). The example/tests/bench opt
  in by passing a cache. (`nullCacheSync` is *not* a default — it would
  FFT-then-discard.)
- **Warm site verified:** `runMultiCompileFull`, after `prePassDomainLog2s`,
  before `runMultiCompile`. Pure builders untouched.

## Pass 2 (completeness): External / SideLoaded slot domains

A recursive circuit verifies previous proofs; each verified-proof position is a
**slot**. Reading a verified proof's VK requires the Lagrange basis at *that
proof's wrap domain* (the `pallas @ <domain>` reads in `shapeCompileData`). So the
pallas domains we touch are the wrap domains of the proofs our slots verify, and
that is decided by each slot's `SlotWrapKey`:

- **`Self`** — verifies a proof from *this same* `compileMulti` program (ordinary
  recursion: a merge node verifying its children, `simple_chain`'s previous link,
  `tree_proof_return`'s recursive slot). All branches of one program share one
  wrap circuit, so a `Self` slot's wrap domain is always the program's own wrap
  domain (`outerWrapDomainLog2`). ⇒ covered by the base warm `pallas @ {own wrap
  domain}`.
- **`External`** — verifies a proof from a *different, separately-compiled*
  program whose VK is baked in at compile time. That VK carries its own
  `vks.wrapDomainLog2`, which may differ from ours, so it reads `pallas @
  vks.wrapDomainLog2` — a domain outside the base set.
- **`SideLoaded`** — verifies a proof whose VK is supplied at *runtime*. The
  domain isn't known at compile, so the circuit handles any legal wrap domain via
  a one-hot selector and bakes in commitments for **all three** legal wrap domains
  `{13, 14, 15}` (= wrap domains for N=0/1/2). So it reads `pallas @ 13, 14, 15`.

**What the base warm (Pass 1) covers.** `vesta @ {all branch step domains}` (from
`prePassDomainLog2s`) + `pallas @ {own wrap domain}`:
- `Self`-slot programs — the transaction base+merge tree, `simple_chain`,
  `tree_proof_return`, everything we run in production and most tests — are **fully
  covered**: every read hits the warmed, persisted basis.
- `External` / `SideLoaded` slots — the extra pallas domains aren't pre-warmed, so
  the lazy closure falls back to kimchi computing them in-process. Still
  **correct**, just **not disk-persisted** (recomputed once per process). The
  pickles `Pickles.Sideload.*` suite uses `SideLoaded` slots and is the one place
  this is observable today.

**The pass (simpler than slot enumeration).** Every legal wrap domain is in
`{13,14,15}` (`wrapDomainLog2ForProofsVerified`, mpv 0/1/2) — the own wrap domain,
each `Self`/`External`/`SideLoaded` slot's verified-proof domain, all of them. So
instead of walking the slot config, the warm just covers the **complete bounded
pallas wrap set `{13,14,15}`** at the warm point, and keeps the (expensive,
unbounded) vesta *step* side precise from the pre-pass. This is exhaustive, not a
guess, and needs no slot/type inspection. Cost: a `Self`-only program warms at
most two small 2^15 pallas bases it won't use — negligible vs. the old broad vesta
`[9..16]`. (This also let the `mpvMax` reflection added in Pass 1 be removed.)
Then the `External`/`SideLoaded` specs (TreeProofReturn, SideLoadedMain) flip from
`Nothing` to `Just lagrangeCache` and persist.

## Implementation passes

1. **Pass 1 — base warm + plumbing.** Add `lagrangeCache :: Maybe SrsCacheSync` to
   `CompileMultiConfig`; warm `vesta @ {step domains}` + `pallas @ {own wrap
   domain}` in `runMultiCompileFull`. Switch `Env`/`SharedSrs`/`mkBenchSrs` to
   generators-only and pass the cache in; delete every domain-list constant.
   Covers all production programs + non-sideload tests with full persistence.
2. **Pass 2 — wrap-set completeness.** Warm the full `{13,14,15}` pallas wrap set
   (exhaustive legal domains) so External/SideLoaded paths are also persisted; flip
   their specs to `Just lagrangeCache`. No slot enumeration needed.

## Validation

- Witness / proof byte-equality suites unchanged (the basis bytes are identical
  whether FFT'd or injected — already asserted by the snarky-kimchi SRS serde
  test and the cross-handle `FsCacheSpec`).
- Run pickles/example/schnorr/circuit-diffs twice against a clean
  `SNARK_SRS_CACHE_DIR`: 1st run computes each used domain once (and only the used
  domains — no `[9..16]` spam), 2nd run shows `[srs-cache] hit` for every basis
  and runs zero FFTs.
- Confirm no domain-list constants remain (`grep -r 'Domains\|\[9' …`).
