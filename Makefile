.PHONY: help all clean build-curves build-snarky build-snarky-bulletproofs build-snarky-groth16 test-curves test-snarky test-core test-bulletproofs test-groth16 test-all-backends run-snarky cargo-check cargo-build cargo-test cargo-fmt cargo-clippy lint crypto-lightweight crypto-bulletproofs crypto-groth16 build-curves-napi build-bulletproofs build-groth16-napi

.DEFAULT_GOAL := help

help: ## Show available commands and their descriptions
	@echo ""
	@echo "Snarky PureScript Zero-Knowledge Circuit Library"
	@echo "==============================================="
	@echo ""
	@echo "Testing Strategy:"
	@echo "  Different backends require different crypto providers:"
	@echo "  - Core packages (curves, snarky): Use crypto-lightweight"
	@echo "  - Bulletproofs: Use crypto-bulletproofs (builds + links bulletproofs NAPI)"
	@echo "  - Groth16: Use crypto-groth16 (builds + links groth16 NAPI)"
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

all: cargo-build build-curves build-snarky ## Build everything

build-curves: ## Build curves package (includes native compilation)
	cd packages/curves && $(MAKE) all

build-snarky: build-curves ## Build snarky package (depends on curves being built)
	cd packages/snarky && npx spago build

build-snarky-bulletproofs: crypto-bulletproofs ## Build snarky-bulletproofs package with bulletproofs crypto
	cd packages/snarky-bulletproofs && npx spago build

build-snarky-groth16: crypto-groth16 ## Build snarky-groth16 package with groth16 crypto
	cd packages/snarky-groth16 && npx spago build

test-curves: build-curves ## Test curves  
	rm -f packages/crypto-provider
	ln -sf curves/curves-napi packages/crypto-provider
	npm install
	cd packages/curves && npx spago test

test-snarky: build-snarky ## Test snarky
	cd packages/snarky && npx spago test

run-snarky: build-snarky ## Run snarky main
	cd packages/snarky && npx spago run

test-core: crypto-lightweight ## Test core packages (curves + snarky) with lightweight crypto
	npx spago test -p curves
	npx spago test -p snarky

test-bulletproofs: crypto-bulletproofs ## Test snarky-bulletproofs with bulletproofs crypto provider
	npx spago test -p snarky-bulletproofs

test-groth16: crypto-groth16 ## Test snarky-groth16 with groth16 crypto provider 
	npx spago test -p snarky-groth16

test-all-backends: ## Test all backends by switching crypto providers (CI-friendly)
	@echo "=== Testing Core Packages (curves + snarky) ===" 
	$(MAKE) test-core
	@echo "=== Testing Bulletproofs Backend ==="
	$(MAKE) test-bulletproofs  
	@echo "=== Testing Groth16 Backend ==="
	$(MAKE) test-groth16
	@echo "=== All backend tests completed successfully ==="

test: test-all-backends ## Test everything with proper crypto provider switching

# Environment variable for pasta curves backend selection
PASTA_CURVES_BACKEND ?= mina-curves

# Helper to determine cargo features based on backend
ifeq ($(PASTA_CURVES_BACKEND),mina-curves)
CURVES_FEATURES = --no-default-features --features mina-curves-backend
else ifeq ($(PASTA_CURVES_BACKEND),arkworks)
CURVES_FEATURES = # Use default features
else
$(error Invalid PASTA_CURVES_BACKEND: $(PASTA_CURVES_BACKEND). Must be 'arkworks' or 'mina-curves')
endif

# Crypto Provider Targets
build-curves-napi: ## Build curves NAPI module with backend selection (set PASTA_CURVES_BACKEND=mina-curves|arkworks)
	@echo "Building curves-napi with backend: $(PASTA_CURVES_BACKEND)"
ifeq ($(PASTA_CURVES_BACKEND),mina-curves)
	cd packages/curves/curves-napi && npm run build:mina-curves
else
	cd packages/curves/curves-napi && npm run build:arkworks
endif
	cd packages/curves && npx spago build

crypto-lightweight: build-curves-napi ## Set up lightweight crypto provider (curves only)
	rm -f packages/crypto-provider
	ln -sf curves/curves-napi packages/crypto-provider
	npm install

crypto-bulletproofs: build-bulletproofs ## Set up bulletproofs crypto provider (curves + bulletproof proving)
	rm -f packages/crypto-provider
	ln -sf snarky-bulletproofs/snarky-bulletproofs-napi packages/crypto-provider
	npm install

build-bulletproofs: ## Build bulletproofs NAPI module with backend selection  
	@echo "Building bulletproofs-napi with backend: $(PASTA_CURVES_BACKEND)"
ifeq ($(PASTA_CURVES_BACKEND),mina-curves)
	cd packages/snarky-bulletproofs/snarky-bulletproofs-napi && npm run build:mina-curves
else
	cd packages/snarky-bulletproofs/snarky-bulletproofs-napi && npm run build:arkworks
endif

build-groth16-napi: ## Build groth16 NAPI module
	npm run build:groth16

crypto-groth16: build-groth16-napi ## Set up groth16 crypto provider
	rm -f packages/crypto-provider
	ln -sf snarky-groth16/snarky-groth16-napi packages/crypto-provider
	npm install

build-groth16: cargo-build ## Build groth16 package
	cd prover/groth16 && cargo build

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
	cd packages/curves && $(MAKE) clean  
	cd packages/snarky && rm -rf output
	-cd packages/snarky-bulletproofs && rm -rf output
	-cd packages/snarky-bulletproofs/snarky-bulletproofs-napi && cargo clean && rm -f *.node
	-cd packages/snarky-groth16 && rm -rf output
	-cd packages/snarky-groth16/snarky-groth16-napi && cargo clean && rm -f *.node
	rm -rf output node_modules target
	rm -f package-lock.json packages/crypto-provider
