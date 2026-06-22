#!/usr/bin/env bash
# tools/lib/common.sh — shared helpers for tools/ scripts.
# Source after setting REPO_ROOT (or equivalent).

die()  { echo "FATAL: $*" >&2; exit 1; }
warn() { echo "WARN: $*" >&2; }
