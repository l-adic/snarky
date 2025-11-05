.PHONY: help all clean build-curves build-snarky test-curves test-snarky run-snarky

.DEFAULT_GOAL := help

help: ## Show available commands and their descriptions
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-15s %s\n", $$1, $$2}'

all: build-curves build-snarky ## Build everything

build-curves: ## Build curves package (includes native compilation)
	cd packages/curves && $(MAKE) all

build-snarky: build-curves ## Build snarky package (depends on curves being built)
	cd packages/snarky && npx spago build

test-curves: build-curves ## Test curves
	cd packages/curves && npx spago test

test-snarky: build-snarky ## Test snarky
	cd packages/snarky && npx spago test

run-snarky: build-snarky ## Run snarky main
	cd packages/snarky && npx spago run

test: test-curves test-snarky ## Test everything

clean: ## Clean everything
	cd packages/curves && $(MAKE) clean
	cd packages/snarky && rm -rf output
	rm -rf output node_modules
	rm -f package-lock.json