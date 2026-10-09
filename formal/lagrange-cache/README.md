# Committed Lean Lagrange bases

The eight tables named in `manifest.json` are committed fixtures. A CI checkout supplies
them directly; no GitHub Actions cache or application proof cache is needed. Each file
contains a prefix of the domain's Lagrange commitments, with one point per SRS chunk.
Consumers requesting fewer commitments reuse that prefix.

From the repository root:

```sh
make check-lagrange-cache
make regenerate-lagrange-cache
```

Regeneration computes every table from the shared `pallas.srs` and `vesta.srs` files,
using `Bulletproof.Ipa.lagrangeBasis` and `Kimchi.Verifier.domainGenerator`. It reads no
old table and requires no application dumps. The manifest records curve, SRS rounds,
domain exponent, chunks, prefix length, table SHA-256 and the input SRS SHA-256 values.
After changes to the SRS, basis algorithm or required domains/prefixes, regenerate,
review the changes, and commit the tables and manifest together.

The Lean CI application job requires cache hits, checks the manifest against the SRS
files it actually loaded, and verifies afterward that the fixtures stayed unchanged.
Outside that job, missing or insufficient tables retain the usual compute-on-miss behavior;
`LAGRANGE_CACHE_DIR` selects a local cache. `LAGRANGE_CACHE_REQUIRED=1` refuses a miss. A
table computed for a domain outside the manifest fails `make check-lagrange-cache` as unlisted
until the manifest is regenerated to list it or the table is removed.

These hashes pin fixture provenance and detect changes. They do not discharge the
capstones' mathematical correspondence between a consumed table and the SRS-derived basis.
