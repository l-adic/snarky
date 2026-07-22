#!/usr/bin/env bash
# The shape-literal gate: no bare structural dimension may appear in a TYPE position.
#
# The kimchi shape constants (Kimchi/Columns.lean) name every structural dimension
# (wCols, permCols, coeffCols, selCount, sigmaRows, litRowCount, tailRowCount,
# batchRows, evalPts). This check enforces their use: any bare 6/7/15/43/44 in a
# type-shaped position — `Fin N`, a `Vector` dimension, a `parseSized` dimension,
# `.take 6`, or an `N * nc` stream size — fails the gate.
#
# Deliberately OUT of scope (the audited policy):
#   * Kimchi/Gate/** — gate-internal constants (S-box exponent, crumb counts,
#     constraint counts), each derived in its gate's preamble;
#   * proof-side arithmetic (`by omega` bounds, position expressions, offsets) —
#     the constants are notations expanding to literals precisely so proofs keep
#     literal arithmetic;
#   * the SRS base `2 ^ σ.k` and verifier.rs line citations in docstrings.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 - <<'EOF'
import re, os, sys
files = []
for root, dirs, fs in os.walk('Kimchi'):
    if 'Gate' in root.split(os.sep):
        continue
    for f in fs:
        if f.endswith('.lean'):
            files.append(os.path.join(root, f))
files += ['KimchiFixture/Kimchi.lean', 'KimchiFixture/PS.lean']

pats = [r'Fin (15|7|6|44|43)\b',
        r'Vector\b[^\n]*?[^\^\w](15|7|6|43|44)\b',
        r'\.take 6\b',
        r'parseSized "[^"]*" (15|7|6)\b',
        r'(44|43) \* nc\b']
bad = 0
for path in files:
    for ln, line in enumerate(open(path), 1):
        code = re.sub(r'--.*', '', line)
        for pat in pats:
            m = re.search(pat, code)
            if m and '2 ^' not in m.group(0):
                print(f"  ✗ {path}:{ln}: {line.strip()[:90]}")
                bad += 1
if bad:
    print(f"✗ {bad} bare structural dimension(s) in type position — "
          "use the Kimchi/Columns.lean constants")
    sys.exit(1)
print("✓ no bare structural dimensions in type position "
      "(the Kimchi/Columns.lean constants are in force)")
EOF
