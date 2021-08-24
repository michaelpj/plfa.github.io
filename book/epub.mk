#################################################################################
# Configuration
#################################################################################

EPUB_DIR          := book
EPUB_TEMPLATE_DIR := $(EPUB_DIR)/templates
EPUB_LUA_DIR      := $(EPUB_DIR)/lua
EPUB_LUA_SCRIPTS  := $(wildcard $(EPUB_LUA_DIR)/*.lua)
MD_DIR            := src
MD_FILES          := README.md $(wildcard $(MD_DIR)/plfa/**/*.md)
FRANKENFONT       := public/webfonts/DejaVu-mononoki-Symbola-Droid.woff


#################################################################################
# Compile PLFA to an EPUB using Pandoc
#################################################################################

.PHONY: epub epub-build
epub: epub-build
epub-build: $(SITE_DIR)/plfa.epub

$(SITE_DIR)/plfa.epub: \
		$(RAW_DIR)/epub.md $(EPUB_DIR)/epub.css $(RAW_DIR)/epub.xml $(FRANKENFONT) \
		$(MD_FILES) $(EPUB_LUA_SCRIPTS) | setup-install-pandoc
	@echo "Building EPUB"
	@$(PANDOC) \
		--strip-comments \
		--css=$(EPUB_DIR)/epub.css \
		--epub-embed-font=$(FRANKENFONT) \
    --epub-metadata=$(RAW_DIR)/epub.xml \
		--indented-code-class=default \
		--lua-filter=$(EPUB_LUA_DIR)/set-default-code-class.lua -M default-code-class=agda \
		--lua-filter=$(EPUB_LUA_DIR)/remove-badges.lua -M badge-url=https://img.shields.io/badge/ \
		--lua-filter=$(EPUB_LUA_DIR)/epub-clean-html.lua \
		--lua-filter=$(EPUB_LUA_DIR)/single-file-links.lua \
		--lua-filter=$(EPUB_LUA_DIR)/single-file-identifiers.lua \
		--standalone \
		--toc --toc-depth=2 \
		--epub-chapter-level=2 \
		$< -o $@


#################################################################################
# Test EPUB with EPUBCheck
#################################################################################

.PHONY: epub-test
epub-test: $(SITE_DIR)/plfa.epub | setup-check-epubcheck
	@echo "Testing EPUB with EPUBCheck"
	@epubcheck $(SITE_DIR)/plfa.epub


#################################################################################
# Tasks for files that are generated by Hakyll
#################################################################################

$(RAW_DIR)/epub.xml: $(EPUB_DIR)/epub.xml
	@make build


#################################################################################
# Clean up and remove generated EPUB
#################################################################################

.PHONY: epub-clean
epub-clean:
	@echo "Cleaning generated files for EPUB"
	@rm -f $(SITE_DIR)/plfa.epub


#################################################################################
# Setup or check dependencies
#################################################################################

.PHONY: setup-check-epubcheck
setup-check-epubcheck:
ifeq (,$(wildcard $(shell which epubcheck)))
	@echo "The command you called requires EPUBCheck"
	@echo "See: https://github.com/w3c/epubcheck"
endif
