.PHONY: help all clean build-crypto test-curves test-snarky test-bulletproofs test-groth16 test-all run-snarky cargo-check cargo-build cargo-test cargo-fmt cargo-clippy lint 

.DEFAULT_GOAL := help

help: ## Show available commands and their descriptions
	@echo ""
	@echo "Snarky PureScript Zero-Knowledge Circuit Library"
	@echo "==============================================="
	@echo ""
	@echo "Unified Crypto Provider:"
	@echo "  Single crypto-provider crate provides all curve operations,"
	@echo "  bulletproofs proving, and groth16 proving functionality."
	@echo ""
	@echo "Pasta Curves Backend Selection:"
	@echo "  Set PASTA_CURVES_BACKEND environment variable to choose field implementation:"
	@echo "  - PASTA_CURVES_BACKEND=mina-curves (default): Use mina-curves from proof-systems (kimchi ecosystem)"
	@echo "  - PASTA_CURVES_BACKEND=arkworks: Use ark-pallas/ark-vesta"
	@echo "  Example: PASTA_CURVES_BACKEND=arkworks make test-bulletproofs"
	@echo ""
	@echo "Available commands:"
	@echo ""
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-20s %s\n", $$1, $$2}'

all: cargo-build build-crypto ## Build everything

# Environment variable for pasta curves backend selection
PASTA_CURVES_BACKEND ?= mina-curves

# Helper to determine npm script based on backend
ifeq ($(PASTA_CURVES_BACKEND),mina-curves)
CRYPTO_BUILD_SCRIPT = build:mina-curves
else ifeq ($(PASTA_CURVES_BACKEND),arkworks)
CRYPTO_BUILD_SCRIPT = build:arkworks
else
$(error Invalid PASTA_CURVES_BACKEND: $(PASTA_CURVES_BACKEND). Must be 'arkworks' or 'mina-curves')
endif

# Unified crypto provider build
build-crypto: ## Build unified crypto-provider with backend selection (set PASTA_CURVES_BACKEND=mina-curves|arkworks)
	@echo "Building crypto-provider with backend: $(PASTA_CURVES_BACKEND)"
	cd packages/crypto-provider && npm run $(CRYPTO_BUILD_SCRIPT)
	npm install

# PureScript package testing
test-curves: build-crypto ## Test curves package
	cd packages/curves && npx spago test

test-snarky: build-crypto ## Test snarky core package  
	cd packages/snarky && npx spago test

run-snarky: build-crypto ## Run snarky main
	cd packages/snarky && npx spago run

test-bulletproofs: build-crypto ## Test snarky-bulletproofs package
	cd packages/snarky-bulletproofs && npx spago test

test-groth16: build-crypto ## Test snarky-groth16 package
	cd packages/snarky-groth16 && npx spago test

test-poseidon: build-crypto ## Test poseidon hash package
	cd packages/poseidon && npx spago test

test-all: ## Test all packages with proper crypto provider
	@echo "=== Testing Core Packages (curves + snarky) ====" 
	$(MAKE) test-curves
	$(MAKE) test-snarky
	@echo "=== Testing Poseidon Hash Package ==="
	$(MAKE) test-poseidon
	@echo "=== Testing Bulletproofs Backend ==="
	$(MAKE) test-bulletproofs  
	@echo "=== Testing Groth16 Backend ===" 
	$(MAKE) test-groth16
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

lint: ## Format, tidy, and lint all code (Rust + PureScript)
	cargo fmt --all
	npx purs-tidy format-in-place 'packages/*/src/**/*.purs' 'packages/*/test/**/*.purs'
	cargo clippy --all-targets -- -D warnings

clean: ## Clean everything
	cargo clean
	cd packages/crypto-provider && cargo clean && rm -f *.node
	cd packages/curves && rm -rf output
	cd packages/snarky && rm -rf output
	-cd packages/snarky-bulletproofs && rm -rf output
	-cd packages/snarky-groth16 && rm -rf output
	rm -rf output node_modules target
	rm -f package-lock.json