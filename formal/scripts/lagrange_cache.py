#!/usr/bin/env python3
"""Check or regenerate the committed Lean Lagrange tables and their SRS provenance."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

FORMAL = Path(__file__).resolve().parents[1]
CACHE = FORMAL / "lagrange-cache"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_manifest(cache):
    manifest = json.loads((cache / "manifest.json").read_text())
    if manifest["formatVersion"] != 1 or set(manifest["srs"]) != {"pallas", "vesta"}:
        raise ValueError("unsupported Lagrange manifest")
    names = set()
    for entry in manifest["tables"]:
        curve = entry["curve"]
        k, log2, chunks, count = (
            entry[key] for key in ("srsRounds", "domainLog2", "chunks", "count")
        )
        if curve not in manifest["srs"] or not all(
            type(value) is int and value > 0 for value in (k, log2, chunks, count)
        ):
            raise ValueError(f"invalid Lagrange table parameters: {entry}")
        expected = f"{curve}-k{k}-2^{log2}-{chunks}c.json"
        if entry["file"] != expected or expected in names:
            raise ValueError(f"invalid or duplicate table name: {entry['file']}")
        if log2 > 32 or chunks != 2 ** max(0, log2 - k) or count > 2 ** log2:
            raise ValueError(f"invalid domain, chunks or prefix: {expected}")
        names.add(expected)
    if not names:
        raise ValueError("empty Lagrange manifest")
    return manifest


def check_table(path, entry):
    points = json.loads(path.read_text())
    if not isinstance(points, list) or len(points) != entry["count"]:
        raise ValueError(f"{path.name}: expected {entry['count']} commitments")
    for row in points:
        if not isinstance(row, list) or len(row) != entry["chunks"]:
            raise ValueError(f"{path.name}: expected {entry['chunks']} chunks per commitment")
        for point in row:
            if not isinstance(point, list) or len(point) != 2 or not all(
                isinstance(x, str) and x.isascii() and x.isdecimal() for x in point
            ):
                raise ValueError(f"{path.name}: expected decimal coordinate pairs")


def srs_hashes(srs_dir):
    return {curve: digest(srs_dir / f"{curve}.srs") for curve in ("pallas", "vesta")}


def check(cache, manifest, srs_dir=None):
    expected = {entry["file"] for entry in manifest["tables"]}
    actual = {path.name for path in cache.glob("*-k*-2^*-*c.json")}
    if actual != expected:
        raise ValueError(
            f"Lagrange table inventory: missing {sorted(expected - actual)}, "
            f"unlisted {sorted(actual - expected)}"
        )
    for entry in manifest["tables"]:
        path = cache / entry["file"]
        if digest(path) != entry["sha256"]:
            raise ValueError(f"{path.name}: differs from the pinned table hash")
        check_table(path, entry)
    if srs_dir is not None:
        for curve, actual_hash in srs_hashes(srs_dir).items():
            if actual_hash != manifest["srs"][curve]["sha256"]:
                raise ValueError(f"{curve}.srs: differs from the Lagrange manifest's SRS")
    print(f"✓ {len(expected)} committed Lagrange tables match their manifest")
    if srs_dir is not None:
        print("✓ Lagrange SRS inputs match their pinned hashes")


def regenerate(cache, manifest, srs_dir):
    inputs = srs_hashes(srs_dir)
    # Generate into an empty directory so a cache hit cannot stand in for recomputation.
    with tempfile.TemporaryDirectory(prefix="lean-lagrange-regenerate-") as temp:
        output = Path(temp)
        subprocess.run(
            ["lake", "exe", "regenerate-lagrange-cache", str(cache / "manifest.json"),
             str(output), str(srs_dir)],
            cwd=FORMAL, check=True,
        )
        for entry in manifest["tables"]:
            check_table(output / entry["file"], entry)
            entry["sha256"] = digest(output / entry["file"])
        if srs_hashes(srs_dir) != inputs:
            raise ValueError("the SRS files changed during regeneration")
        for curve, sha in inputs.items():
            manifest["srs"][curve] = {"file": f"{curve}.srs", "sha256": sha}
        # Publish only after every table was computed and checked; publish the manifest last.
        for entry in manifest["tables"]:
            target = cache / entry["file"]
            staging = target.with_suffix(".json.tmp")
            staging.write_bytes((output / entry["file"]).read_bytes())
            os.replace(staging, target)
        staging = cache / "manifest.json.tmp"
        staging.write_text(json.dumps(manifest, indent=2) + "\n")
        os.replace(staging, cache / "manifest.json")
    check(cache, manifest, srs_dir)
    print("Review and commit the table and manifest changes together.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "regenerate"))
    parser.add_argument("--cache-dir", type=Path, default=CACHE)
    parser.add_argument("--srs-dir", type=Path)
    args = parser.parse_args()
    cache = args.cache_dir.resolve()
    manifest = read_manifest(cache)
    if args.mode == "regenerate":
        srs_dir = (args.srs_dir or FORMAL.parent / "srs-cache").resolve()
        regenerate(cache, manifest, srs_dir)
    else:
        check(cache, manifest, args.srs_dir.resolve() if args.srs_dir else None)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"✗ Lagrange cache: {error}", file=sys.stderr)
        sys.exit(1)
