#!/bin/bash

# Create srs-cache directory if it doesn't exist
mkdir -p srs-cache

echo "Downloading test_pallas.srs..."
curl -L -o srs-cache/test_pallas.srs https://github.com/o1-labs/proof-systems/raw/refs/heads/master/srs/test_pallas.srs

echo "Downloading pallas.srs..."
curl -L -o srs-cache/pallas.srs https://github.com/o1-labs/proof-systems/raw/refs/heads/master/srs/pallas.srs


echo "Downloads completed!"
