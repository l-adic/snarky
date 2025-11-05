.PHONY: help all clean build-curves build-snarky test-curves test-snarky run-snarky

.DEFAULT_GOAL := help

help: ## Show available commands and their descriptions
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-15s %s\n", $$1, $$2}'

all: build-curves build-snarky ## Build everything

build-curves: ## Build curves package (includes native compilation)
	cd packages/curves && $(MAKE) all

build-snarky: build-curves ## Build snarky package (depends on curves being built)
	cd packages/snarky && spago build
	# Copy native modules to the global output for snarky to find
	mkdir -p output/Snarky.Curves.Pallas output/Snarky.Curves.Vesta output/Snarky.Curves.BN254
	cp packages/curves/src/Snarky/Curves/pallas-napi.node output/Snarky.Curves.Pallas/pallas-napi.node
	cp packages/curves/src/Snarky/Curves/vesta-napi.node output/Snarky.Curves.Vesta/vesta-napi.node
	cp packages/curves/src/Snarky/Curves/bn254-napi.node output/Snarky.Curves.BN254/bn254-napi.node

test-curves: build-curves ## Test curves
	cd packages/curves && spago test

test-snarky: build-snarky ## Test snarky
	cd packages/snarky && spago test

run-snarky: build-snarky ## Run snarky main
	cd packages/snarky && spago run

test: test-curves test-snarky ## Test everything

clean: ## Clean everything
	cd packages/curves && $(MAKE) clean
	cd packages/snarky && rm -rf output
	rm -rf output
	# Clean legacy artifacts
	rm -rf curves-napi/ pallas-napi/ pasta-curves/ src/ test/
	rm -f *.node spago.lock.bak