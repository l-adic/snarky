# Pickles Linearization Code Generation Pipeline
#
# This Makefile runs the two-stage code generation:
# 1. Rust binary extracts linearization from Kimchi → JSON
# 2. PureScript generator transforms JSON → .purs modules
#
# Output goes to ../pickles/src/Pickles/Linearization/
#
# A third stage, `lean`, renders the same JSON as Lean token modules for formal/pickles.
# It is NOT part of `generate`: it needs a Lean toolchain, which the PureScript CI jobs
# that run `make gen-linearization` do not install, and its output is committed rather
# than regenerated per build. Run it via `make gen-linearization-lean` at the repo root.

RUST_BIN := rust
JSON_DIR := $(RUST_BIN)/output
OUTPUT_DIR := ../pickles/src/Pickles/Linearization

.PHONY: all clean generate json purescript lean

all: generate

# Full pipeline: JSON then PureScript
generate: json purescript

# Step 1: Generate JSON from Kimchi using Rust
json:
	@echo "==> Generating linearization JSON from Kimchi..."
	@mkdir -p $(JSON_DIR)
	cd ../.. && LINEARIZATION_JSON_DIR=$(CURDIR)/$(JSON_DIR) cargo run --release -p gen-linearization
	@echo "==> JSON files generated in $(JSON_DIR)"

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

# Step 3 (separate; see the header): Generate the Lean token modules from the same JSON.
# Unlike Pallas.purs / Vesta.purs these outputs are COMMITTED: formal/'s CI checks out
# without the mina submodule (.github/workflows/lean.yml sets `submodules: false`), so it
# cannot regenerate them and must read them from the tree. Re-run this target
# (`make gen-linearization-lean` at the root) on a proof-systems bump and commit the diff.
lean: json
	@echo "==> Generating Lean token modules from JSON..."
	cd ../../formal/pickles && PATH="$$HOME/.elan/bin:$$PATH" \
	  LINEARIZATION_JSON_DIR=$(CURDIR)/$(JSON_DIR) lake env lean --run scripts/gen_tokens.lean

# Clean generated files
clean:
	rm -f $(JSON_DIR)/*.json
	rm -f $(OUTPUT_DIR)/Pallas.purs
	rm -f $(OUTPUT_DIR)/Vesta.purs
	rm -f ../../formal/pickles/Pickles/Linearization/Fp.lean
	rm -f ../../formal/pickles/Pickles/Linearization/Fq.lean

# Show what would be generated
info:
	@echo "JSON directory: $(JSON_DIR)"
	@echo "Output directory: $(OUTPUT_DIR)"
	@echo "Expected outputs:"
	@echo "  - $(OUTPUT_DIR)/Pallas.purs"
	@echo "  - $(OUTPUT_DIR)/Vesta.purs"
