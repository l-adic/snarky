# Run from formal/paper/. All generated files and caches stay here.
# Requires Tectonic and rsvg-convert (librsvg).
PAPER_DIR := $(CURDIR)
# Set TECTONIC_FLAGS=--only-cached to use an existing cache offline.
TECTONIC_FLAGS ?=

.PHONY: summary
summary: build/reconstruction-draft-graphic.pdf
	mkdir -p build .cache/tectonic
	TECTONIC_CACHE_DIR="$(PAPER_DIR)/.cache/tectonic" XDG_CACHE_HOME="$(PAPER_DIR)/.cache" tectonic $(TECTONIC_FLAGS) --keep-logs --outdir build summary.tex
	cp build/summary.pdf summary.pdf

build/reconstruction-draft-graphic.pdf: reconstruction-draft.svg Makefile
	mkdir -p build
	rsvg-convert -f pdf1.5 -o $@ $<
