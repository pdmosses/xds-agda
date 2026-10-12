SOURCES := ../agda
MODULES := Background Notation Examples Properties Tests
PROTECT := docs/index.md docs/Abstract.md docs/Library/index.md docs/Meta-notation.md
SERVER  := 8002

include agda-pages/agda-pages.mk

# `make agda-unhide` removes hiding markup in `*.lagda.md` files in SOURCES

LAGDA-MD-FILES := \
	$(sort \
	  $(shell find $(SOURCES) -name '*.lagda.md'))

agda-unhide:
	@for file in $(LAGDA-MD-FILES) ; do \
	    sd -- '--"hide"\n' '' $${file} ; \
	    sd '\n--"/hide"' '' $${file} ; \
	    sd '@latex[^@]*@/latex' '' $${file} ; \
	done
	@echo "Removed hiding markup from .lagda.md files in $(SOURCES)"
