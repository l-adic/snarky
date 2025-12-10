.PHONY: help all clean build-curves build-snarky build-snarky-bulletproofs build-groth16 test-curves test-snarky run-snarky cargo-check cargo-build cargo-test cargo-fmt cargo-clippy crypto-lightweight crypto-full build-bulletproofs

.DEFAULT_GOAL := help

help: ## Show available commands and their descriptions
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-15s %s\n", $$1, $$2}'

all: cargo-build build-curves build-snarky ## Build everything

build-curves: crypto-lightweight ## Build curves package (includes native compilation)
	cd packages/curves && $(MAKE) all

build-snarky: build-curves ## Build snarky package (depends on curves being built)
	cd packages/snarky && npx spago build

build-snarky-bulletproofs: crypto-full ## Build snarky-bulletproofs package with full crypto
	cd packages/snarky-bulletproofs && npx spago build

test-curves: build-curves ## Test curves
	cd packages/curves && npx spago test

test-snarky: build-snarky ## Test snarky
	cd packages/snarky && npx spago test

run-snarky: build-snarky ## Run snarky main
	cd packages/snarky && npx spago run

test: crypto-full ## Test everything
	npx spago test

# Crypto Provider Targets
crypto-lightweight: ## Set up lightweight crypto provider (curves only)
	rm -f packages/crypto-provider
	ln -sf curves/curves-napi packages/crypto-provider
	npm install

crypto-full: build-bulletproofs ## Set up full crypto provider (curves + bulletproof proving)
	rm -f packages/crypto-provider
	ln -sf snarky-bulletproofs/snarky-bulletproofs-napi packages/crypto-provider
	npm install

build-bulletproofs: ## Build bulletproofs NAPI module
	cd packages/snarky-bulletproofs/snarky-bulletproofs-napi && npm install && npm run build

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

clean: ## Clean everything
	cargo clean
	cd packages/curves && $(MAKE) clean  
	cd packages/snarky && rm -rf output
	-cd packages/snarky-bulletproofs && rm -rf output
	-cd packages/snarky-bulletproofs/snarky-bulletproofs-napi && cargo clean && rm -f *.node
	rm -rf output node_modules target
	rm -f package-lock.json packages/crypto-provider
