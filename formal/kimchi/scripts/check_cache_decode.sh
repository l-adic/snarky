#!/usr/bin/env bash
# Check the proof-cache decoder (`KimchiFixture.Cache`) against the Rust-produced kimchi
# proof fixture: the wrap key through `SimpleChain.json`, the proof through the serde file
# the fixture was rendered from. Driver: scripts/check_cache_decode.lean. Requires a prior
# `lake build KimchiFixture`. Standalone (this package's own workspace); from the
# aggregator use:
#   cd formal && lake env lean --run kimchi/scripts/check_cache_decode.lean
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run scripts/check_cache_decode.lean
