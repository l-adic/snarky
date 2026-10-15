#!/usr/bin/env bash
# Certify reconstruction sidecars against their independent foreign constraint-system dumps.
# Reject missing, malformed and mismatching dumps before reporting certification success.
# Reject finite but incorrect Step and Wrap Lagrange tables against the shared SRSs.
# Then require located failures and dependency blocking beside an intact application:
#   TwoPhaseChain: malformed sidecar, rejected while loading;
#   RecurseOverChunks: chunks2's rule input disagrees with its shape, rejected during assembly;
#   HeterogeneousPrevs: child's rule gains a constraint but keeps its keys, rejected by key checking.
# NoRecursionReturn still certifies beside the damaged applications.
#
# Usage: PICKLES_DUMP_DIR=<dumps> scripts/check_certify_failures.sh   (from formal/, after
# `lake build certify-application`)
set -euo pipefail
cd "$(dirname "$0")/.."
dumps="${PICKLES_DUMP_DIR:?PICKLES_DUMP_DIR is not set}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for app in NoRecursionReturn TwoPhaseChain RecurseOverChunks HeterogeneousPrevs; do
  cp -R "$dumps/$app" "$work/"
done

log="$work/success.log"
if ! PICKLES_DUMP_DIR="$work" APPS=NoRecursionReturn \
    lake exe certify-application > "$log" 2>&1; then
  echo "✗ certification failed for intact reconstruction inputs and circuit dumps"
  tail -12 "$log"
  exit 1
fi
expect() { # $1 = an expected message
  grep -Fq -- "$1" "$log" || {
    echo "✗ no line containing '$1'"
    tail -12 "$log"
    exit 1
  }
  echo "✓ observed: $1"
}
expect "✓ 1 application(s) certified"
expect "✓ NoRecursionReturn/nrr: imported indices match the certified Lean indices"

for damage in missing malformed step wrap; do
  python3 - "$work/NoRecursionReturn/nrr.json" "$damage" <<'PY'
import json
from pathlib import Path
import sys

path, damage = Path(sys.argv[1]), sys.argv[2]
if damage == 'missing':
    path.unlink()
elif damage == 'malformed':
    path.write_text('{')
else:
    data = json.loads(path.read_text())
    circuit = (data['branches'][0]['stepMain'] if damage == 'step' else data['wrapMain'])['circuit']
    # Mutate a non-public row; the sidecar, keys and other circuit stay intact.
    coeffs = circuit['gates'][circuit['publicInputSize']]['coeffs']
    if coeffs:
        coeffs[0] = str(int(coeffs[0]) + 1)
    else:
        coeffs.append('1')
    path.write_text(json.dumps(data))
PY
  log="$work/$damage-dump.log"
  if PICKLES_DUMP_DIR="$work" APPS=NoRecursionReturn \
      lake exe certify-application > "$log" 2>&1; then
    echo "✗ certification accepted a $damage circuit dump"
    tail -12 "$log"
    exit 1
  fi
  case "$damage" in
    missing|malformed) expect "✗ NoRecursionReturn/nrr: comparison dump:" ;;
    step) expect "✗ NoRecursionReturn/nrr: the imported indices differ at step 0: row 1, coefficient 0" ;;
    wrap) expect "✗ NoRecursionReturn/nrr: the imported indices differ at wrap: row 40, coefficient 0" ;;
  esac
  expect "✗ 1 of 1 application(s) failed:"
  cp "$dumps/NoRecursionReturn/nrr.json" "$work/NoRecursionReturn/nrr.json"
done

# Keep the points finite and the table dimensions unchanged: ordinary point and shape
# checks cannot detect this substitution. Certification must recompute the basis.
for curve in vesta pallas; do
  cache="$work/lagrange-$curve"
  cp -R "${LAGRANGE_CACHE_DIR:-lagrange-cache}" "$cache"
  python3 - "$cache" "$curve" <<'PY'
import json
from pathlib import Path
import sys

cache, curve = Path(sys.argv[1]), sys.argv[2]
for path in cache.glob(f'{curve}-k*-2^*-*c.json'):
    data = json.loads(path.read_text())
    assert len(data) > 1 and data[0] != data[1]
    data[0] = data[1]
    path.write_text(json.dumps(data))
PY
  log="$work/$curve-table.log"
  if PICKLES_DUMP_DIR="$work" LAGRANGE_CACHE_DIR="$cache" APPS=HeterogeneousPrevs \
      lake exe certify-application > "$log" 2>&1; then
    echo "✗ certification accepted a corrupted $curve Lagrange table"
    tail -12 "$log"
    exit 1
  fi
  if [ "$curve" = vesta ]; then
    expect "setup: wrap verifying step"
  else
    expect "setup: step"
  fi
  expect "Lagrange table differs from the SRS-derived basis"
done

python3 - "$work" <<'PY'
import json
from pathlib import Path
import sys

work = Path(sys.argv[1])
(work / 'TwoPhaseChain/shapes/two_phase_chain.json').write_text('{')

path = work / 'RecurseOverChunks/shapes/chunks2.json'
data = json.loads(path.read_text())
data['rules'][0]['inputSize'] += 1
path.write_text(json.dumps(data))

path = work / 'HeterogeneousPrevs/shapes/child.json'
data = json.loads(path.read_text())
rule = data['rules'][0]
assert rule['inputSize'] > 0, 'the child fixture must have an input to constrain'
rule['ops'].append({'constraint': {'basic': {'square': [{'var': 0}, {'var': 0}]}}})
path.write_text(json.dumps(data))
PY

log="$work/failures.log"
if PICKLES_DUMP_DIR="$work" \
    APPS=NoRecursionReturn,TwoPhaseChain,RecurseOverChunks,HeterogeneousPrevs \
    lake exe certify-application > "$log" 2>&1; then
  echo "✗ exit status 0 with three damaged applications"
  tail -12 "$log"
  exit 1
fi
expect "✗ TwoPhaseChain/two_phase_chain: sidecar:"
expect "✗ RecurseOverChunks/chunks2: the rule's input differs from the application schema"
expect "✗ RecurseOverChunks/recurse: blocked by the failure of RecurseOverChunks/chunks2"
expect "✗ HeterogeneousPrevs/child: key: step 0:"
expect "✗ HeterogeneousPrevs/application: blocked by certification failure of HeterogeneousPrevs/child"
expect "✓ NoRecursionReturn/nrr: certified"
expect "✗ 5 of 6 application(s) failed:"
echo "── certify-application regressions OK ──"
