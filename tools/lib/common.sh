#!/usr/bin/env bash
# tools/lib/common.sh — shared helpers for tools/ scripts.
# Source after setting REPO_ROOT (or equivalent).

die()  { echo "FATAL: $*" >&2; exit 1; }
warn() { echo "WARN: $*" >&2; }

# Put the mina submodule's local opam switch (`mina/_opam`, populated from
# `mina/opam.export`; see mina/README-dev.md) on the environment of the
# calling shell, so `dune` builds and runs the OCaml dumpers. This is the
# only build environment the fixture tooling uses: no nix, no switch
# inherited from the shell, and no prebuilt kimchi-stubs — with
# KIMCHI_STUBS / KIMCHI_STUBS_STATIC_LIB set, dune's stubs rule copies that
# static lib instead of building the in-tree proof-systems, so a dumper
# built under a stale one silently proves with the wrong verifier.
#
#   mina_switch_env <repo-root>
mina_switch_env() {
  local switch="$1/mina/_opam"
  [ -x "$switch/bin/dune" ] \
    || die "no opam switch at $switch (mina/README-dev.md: opam switch import opam.export)"
  export PATH="$switch/bin:$PATH" \
    OPAM_SWITCH_PREFIX="$switch" \
    CAML_LD_LIBRARY_PATH="$switch/lib/stublibs"
  unset KIMCHI_STUBS KIMCHI_STUBS_STATIC_LIB
}
