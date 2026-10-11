.PHONY: lean tex go

# Build all examples through the configured default Lake target.
lean:
	lake build

# Clean only this document's artifacts, including when a TeX or BibTeX pass fails.
TEXFILE ?=
tex:
	@set -eu; \
	if [ -z "$(TEXFILE)" ]; then echo "usage: make tex TEXFILE=path/to/file.tex"; exit 1; fi; \
	cd "$(dir $(TEXFILE))"; \
	Base="$(notdir $(basename $(TEXFILE)))"; \
	trap 'latexmk -c "$$Base.tex" >/dev/null 2>&1 || :; \
	      rm -f "$$Base.log" "$$Base.aux" "$$Base.out" "$$Base.toc" "$$Base.fls" \
	            "$$Base.fdb_latexmk" "$$Base.synctex.gz" "$$Base.bbl" "$$Base.blg"' 0; \
	latexmk -pdf -interaction=nonstopmode -halt-on-error "$$Base.tex"

# Use the local Go toolchain without requiring the caller to export PATH.
export PATH := $(HOME)/.local/go/bin:$(PATH)

# The default example uses pure-Go Gonum, with no native BLAS linking.
GOFILE ?=
go:
	@if [ -z "$(GOFILE)" ]; then echo "usage: make go GOFILE=path/to/file.go"; exit 1; fi
	CGO_ENABLED=0 go run "$(GOFILE)"
