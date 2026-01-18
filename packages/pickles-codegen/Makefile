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

.PHONY: all clean generate json purescript

all: generate

# Full pipeline: JSON then PureScript
generate: json purescript

# Step 1: Generate JSON from Kimchi using Rust
json:
	@echo "==> Generating linearization JSON from Kimchi..."
	@mkdir -p $(JSON_DIR)
	cd ../.. && cargo run --release -p gen-linearization
	@echo "==> JSON files generated in $(JSON_DIR)"

# Step 2: Generate PureScript from JSON
purescript: json
	@echo "==> Generating PureScript modules from JSON..."
	@mkdir -p $(OUTPUT_DIR)
	LINEARIZATION_JSON_DIR=$(CURDIR)/$(JSON_DIR) \
	LINEARIZATION_OUTPUT_DIR=$(CURDIR)/$(OUTPUT_DIR) \
	spago run -p pickles-codegen
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
