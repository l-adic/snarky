#!/bin/bash

# Download SRS files from proof-systems repo if not already present.
# Skips files that already exist (e.g., from CI cache).

SRS_BASE_URL="https://github.com/o1-labs/proof-systems/raw/refs/heads/master/srs"

mkdir -p srs-cache

for f in test_pallas.srs test_vesta.srs pallas.srs vesta.srs; do
  if [ -f "srs-cache/$f" ]; then
    echo "$f already exists, skipping"
    continue
  fi
  echo "Downloading $f..."
  curl -fL -o "srs-cache/$f" "$SRS_BASE_URL/$f"
done

echo "SRS cache ready."
