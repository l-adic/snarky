#!/usr/bin/env bash
# tools/mina-env.sh — run a command under the mina submodule's opam switch
# (`mina_switch_env` in tools/lib/common.sh), for callers that cannot
# source a bash function, such as the Makefile:
#
#   tools/mina-env.sh dune exec src/lib/crypto/pickles/dump_x/dump_x.exe
#
# The command runs in the current directory.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/common.sh"
mina_switch_env "$REPO_ROOT"
exec "$@"
