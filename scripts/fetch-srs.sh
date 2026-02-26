#!/bin/bash

# Copy SRS files from the mina submodule to the srs-cache directory.
# Using the submodule's files ensures version consistency with our
# proof-systems dependency (avoids downloading from GitHub master
# which may differ or fail due to rate limiting).

SRS_SRC="mina/src/lib/crypto/proof-systems/srs"

if [ ! -d "$SRS_SRC" ]; then
  echo "Error: mina submodule not initialized. Run: git submodule update --init --recursive"
  exit 1
fi

mkdir -p srs-cache

for f in test_pallas.srs test_vesta.srs pallas.srs vesta.srs; do
  if [ ! -f "$SRS_SRC/$f" ]; then
    echo "Warning: $SRS_SRC/$f not found, skipping"
    continue
  fi
  echo "Copying $f from submodule..."
  cp "$SRS_SRC/$f" "srs-cache/$f"
done

echo "SRS cache populated from submodule."
