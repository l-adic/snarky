.PHONY: help all clean build-napi test-curves test-snarky test-pickles-circuit-diffs test-libs test-all run-snarky cargo-check cargo-build cargo-test cargo-fmt cargo-clippy lint lean-build lean-check-fixtures lean-check-reconstruction dump-fixtures lean-style lean-style-fix build-ps gen-linearization dep-graph pickles-inventory

.DEFAULT_GOAL := help

# Disk proof-cache root for the pickles tests. Absolute (via CURDIR =
# repo root) so it resolves regardless of spago's cwd — tests run both
# as `spago test -p pickles` (repo root) and `cd packages/pickles &&
# spago test` (the recipes below / CI). The pickles tests read this via
# `lookupEnv "PICKLES_PROOF_CACHE_DIR"`; unset => caching disabled
# (every prove runs for real). Override on the CLI to relocate it.
PICKLES_PROOF_CACHE_DIR ?= $(CURDIR)/packages/pickles/test/fixtures/proof-cache
export PICKLES_PROOF_CACHE_DIR

help: ## Show available commands and their descriptions
	@echo ""
	@echo "Snarky PureScript Zero-Knowledge Circuit Library"
	@echo "==============================================="
	@echo ""
	@echo "Native crypto backend: kimchi-napi (upstream proof-systems via"
	@echo "napi-rs). Field/curve/Poseidon primitives live in pasta-runtime"
	@echo "(vendored from o1js). The legacy `snarky-crypto` (crypto-provider)"
	@echo "shim is gone; nothing in production routes through Rust except"
	@echo "the kimchi-napi prove/verify path."
	@echo ""
	@echo "Available commands:"
	@echo ""
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-20s %s\n", $$1, $$2}'

all: cargo-build build-napi ## Build everything

# kimchi-napi rebuild (the only Rust-backed npm workspace package after
# the snarky-crypto cleanup).
build-napi: ## Build kimchi-napi native binding
	@echo "Building kimchi-napi"
	cd packages/kimchi-napi && npm run build
	npm install

build-ps: ## Build all the purescript packages
	@echo "building PS packages"
	npm run build:ps

# PureScript package testing
test-curves: build-napi ## Test curves package
	cd packages/curves && npx spago build && npx spago run --main Test.Snarky.Curves.Main

test-snarky: build-napi ## Test snarky core package
	cd packages/snarky && npx spago test

run-snarky: build-napi ## Run snarky main
	cd packages/snarky && npx spago run

test-poseidon: build-napi ## Test poseidon hash package
	cd packages/poseidon && npx spago test

test-kimchi: build-napi ## Test poseidon hash package
	cd packages/snarky-kimchi && npx spago test

test-random-oracle: build-napi ## Test random-oracle package
	cd packages/random-oracle && npx spago test

test-merkle-tree: build-napi ## Test merkle-tree package
	cd packages/merkle-tree && npx spago test

test-example: build-napi ## Test the example library (plain backend, root workspace; the TUI/web frontends are a separate backend-es workspace under packages/example/app)
	npx spago test -p example

test-pickles: build-napi gen-linearization ## Test pickles package (requires codegen)
	cd packages/pickles && npx spago test

test-pickles-circuit-diffs: build-napi gen-linearization fixtures-unpack ## Test pickles circuit diffs package (requires codegen)
	cd packages/pickles-circuit-diffs && npx spago test

test-libs: ## Test every package EXCEPT example and pickles-circuit-diffs (each its own CI parallel job)
	@echo "=== Generating Linearization Code ==="
	$(MAKE) gen-linearization
	$(MAKE) build-ps
	@echo "=== Testing Core Packages (curves + snarky) ===="
	$(MAKE) test-curves
	$(MAKE) test-snarky
	@echo "=== Testing Poseidon Hash Package ==="
	$(MAKE) test-poseidon
	@echo "=== Testing Kimchi Backend ==="
	$(MAKE) test-kimchi
	@echo "=== Testing Random Oracle ==="
	$(MAKE) test-random-oracle
	@echo "=== Testing merkle-tree ==="
	$(MAKE) test-merkle-tree
	@echo "=== Testing Pickles ==="
	$(MAKE) test-pickles
	@echo "=== Library tests completed successfully ==="

test-all: test-libs ## Test all packages with proper crypto provider
	@echo "=== Testing Example ==="
	$(MAKE) test-example
	@echo "=== Testing Pickles Circuit Diffs ==="
	$(MAKE) test-pickles-circuit-diffs
	@echo "=== All tests completed successfully ==="

test: test-all ## Test everything

# Rust cargo commands
cargo-check: ## Check all Rust packages in workspace
	cargo check --workspace

cargo-build: ## Build all Rust packages in workspace
	cargo build --workspace

cargo-test: ## Test all Rust packages in workspace
	cargo test --workspace

cargo-fmt: ## Format all Rust code in workspace
	cargo fmt --all

cargo-clippy: ## Run clippy lints on workspace
	cargo clippy --workspace -- -D warnings

gen-linearization: build-napi ## Generate Kimchi linearization PureScript modules
	cd packages/pickles-codegen && $(MAKE) generate

lint: ## Format, tidy, and lint all code (Rust + PureScript + Lean)
	cargo fmt --all
	npx purs-tidy format-in-place 'packages/*/src/**/*.purs' 'packages/*/test/**/*.purs'
	bash formal/scripts/check-style.sh --fix
	cargo clippy --all-targets -- -D warnings

lean-build: ## Build the Lean (formal/) project
	cd formal && PATH="$$HOME/.elan/bin:$$PATH" lake build

lean-check-fixtures: lean-build ## Run the verified checker on every committed circuit fixture (asserts check = true; exits non-zero on any false)
	cd formal && PATH="$$HOME/.elan/bin:$$PATH" lake env lean --run Main.lean

lean-check-reconstruction: lean-build ## Check the reconstructed step-circuits (vbmCircuit/emCircuit/esCircuit) accept the real dumped chains and reject tampers
	cd formal && PATH="$$HOME/.elan/bin:$$PATH" lake env lean --run CheckReconstruction.lean

dump-fixtures: build-napi ## Regenerate formal/fixtures/*.json from real compiled circuits (needs the native backend)
	@echo "Compiling the dumpers (only the build matters; the spec runner may trip on pickles codegen)"
	-npx spago test -p snarky-kimchi -- --example "__compile_dumpers_only__"
	node -e "import('./output/Test.Snarky.Circuit.Kimchi.DumpAddComplete/index.js').then(m=>m.dumpAll())"

lean-style: ## Check Lean style (<=100 cols, no trailing ws/tabs, final newline)
	bash formal/scripts/check-style.sh

lean-style-fix: ## Auto-fix mechanical Lean style (trailing whitespace, final newline)
	bash formal/scripts/check-style.sh --fix

clean: ## Clean everything
	cargo clean
	cd packages/kimchi-napi && rm -f *.node
	cd packages/curves && rm -rf output
	cd packages/snarky && rm -rf output
	rm -rf output node_modules target
	rm -f package-lock.json

# Generate workspace module dependency graph (requires deps.json + graphviz)
# Usage:
#   make dep-graph                                          # all workspace packages
#   make dep-graph EXCLUDE=<pkg1>,<pkg2>                    # exclude packages (comma-separated)
#   make dep-graph CLOSURE=pickles                          # only pickles and its transitive deps
EXCLUDE ?=
CLOSURE ?=
dep-graph: ## Generate module dependency graph as deps.svg
	node workspace-deps.js --exclude $(EXCLUDE) $(if $(CLOSURE),--closure $(CLOSURE))

.PHONY: pickles-inventory
pickles-inventory: ## Generate analysis/pickles-inventory.md (Phase 1 of module reorg)
	node pickles-inventory.js

.PHONY: fetch-srs
fetch-srs: ## Download the srs-cache from github
	sh ./scripts/fetch-srs.sh

.PHONY: fixtures-unpack
fixtures-unpack: ## Decompress committed chunk fixtures (idempotent; prereq of circuit-diff tests)
	bash ./scripts/fixtures.sh unpack

.PHONY: fixtures-pack
fixtures-pack: ## Compress chunk fixtures after regen, before committing the *.gz
	bash ./scripts/fixtures.sh pack

.PHONY: clean-proof-cache
clean-proof-cache: ## Wipe the disk proof-cache (forces regeneration of cached step/wrap proofs)
	rm -rf "$(PICKLES_PROOF_CACHE_DIR)"

.PHONY: dump-schnorr-signature-proof
dump-schnorr-signature-proof: ## Generate fresh Schnorr kimchi proof fixtures (3 deterministic cases) under packages/schnorr/test/fixtures/schnorr_signature_proof{,_2,_3}
	mkdir -p packages/schnorr/test/fixtures/schnorr_signature_proof \
	         packages/schnorr/test/fixtures/schnorr_signature_proof_2 \
	         packages/schnorr/test/fixtures/schnorr_signature_proof_3
	cd mina && KIMCHI_DETERMINISTIC_SEED=42 nix develop "git+file://$$PWD?submodules=1" --command \
	  dune exec src/lib/crypto/pickles/dump_schnorr_signature_proof/dump_schnorr_signature_proof.exe -- \
	  ../packages/schnorr/test/fixtures/schnorr_signature_proof

.PHONY: dump-schnorr-signatures
dump-schnorr-signatures: ## Generate raw Schnorr signature test vectors (pure-verify) under packages/schnorr/test/fixtures/schnorr_signatures
	mkdir -p packages/schnorr/test/fixtures/schnorr_signatures
	cd mina && nix develop "git+file://$$PWD?submodules=1" --command \
	  dune exec src/lib/crypto/pickles/dump_schnorr_signatures/dump_schnorr_signatures.exe -- \
	  ../packages/schnorr/test/fixtures/schnorr_signatures
