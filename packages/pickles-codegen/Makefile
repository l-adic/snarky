# Pickles Linearization Code Generation Pipeline
#
# This Makefile runs the two-stage code generation:
# 1. Rust binary extracts linearization from Kimchi → JSON
# 2. PureScript generator transforms JSON → .purs modules
#
# Output goes to ../pickles/src/Pickles/Linearization/

RUST_BIN := rust
JSON_DIR := $(RUST_BIN)/output
OUTPUT_DIR := ../pickles/src/Pickles/Linearization
# Second sink: the Lean tree reads the SAME dump, but as a committed, sha256-pinned
# fixture — `$(JSON_DIR)` is gitignored, and formal/'s CI checks out without submodules
# and never regenerates. One generator, two destinations, so the copies cannot drift.
FORMAL_FIXTURES := ../../formal/pickles/fixtures

.PHONY: all clean generate json purescript

all: generate

# Full pipeline: JSON then PureScript
generate: json purescript

# Step 1: Generate JSON from Kimchi using Rust
json:
	@echo "==> Generating linearization JSON from Kimchi..."
	@mkdir -p $(JSON_DIR)
	cd ../.. && LINEARIZATION_JSON_DIR=$(CURDIR)/$(JSON_DIR) cargo run --release -p gen-linearization
	@echo "==> JSON files generated in $(JSON_DIR)"
	@mkdir -p $(FORMAL_FIXTURES)
	cp $(JSON_DIR)/pallas_scalar_field.json $(JSON_DIR)/vesta_scalar_field.json \
	  $(FORMAL_FIXTURES)/
	@echo "==> Copied to $(FORMAL_FIXTURES) (committed; re-pin with"
	@echo "    formal/scripts/check_fixtures_manifest.sh --regen)"

# Step 2: Generate PureScript from JSON
# Note: we use `spago build` + `node` instead of `spago run` because
# `spago run` calls `purs graph` on the full workspace, which fails
# when the generated Pallas/Vesta modules don't exist yet.
purescript: json
	@echo "==> Generating PureScript modules from JSON..."
	@mkdir -p $(OUTPUT_DIR)
	cd ../.. && npx spago build -p pickles-codegen
	LINEARIZATION_JSON_DIR=$(CURDIR)/$(JSON_DIR) \
	LINEARIZATION_OUTPUT_DIR=$(CURDIR)/$(OUTPUT_DIR) \
	node -e "import('./../../output/Pickles.Linearization.Main/index.js').then(m => m.main())"
	@echo "==> PureScript modules generated in $(OUTPUT_DIR)"

# Clean generated files
clean:
	rm -f $(JSON_DIR)/*.json
	rm -f $(OUTPUT_DIR)/Pallas.purs
	rm -f $(OUTPUT_DIR)/Vesta.purs

# Show what would be generated
info:
	@echo "JSON directory: $(JSON_DIR)"
	@echo "Output directory: $(OUTPUT_DIR)"
	@echo "Expected outputs:"
	@echo "  - $(OUTPUT_DIR)/Pallas.purs"
	@echo "  - $(OUTPUT_DIR)/Vesta.purs"
