# This Makefile is meant to regenerate the OCaml source snapshot of
# the Steel plugin and the header files for the Steel C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: build
build:
	+$(MAKE) -C .. all

# Extraction rules assume that a snapshot has already been compiled.

.PHONY: extract-ocaml
extract-ocaml: extract-steel-plugin extract-extraction

.PHONY: extract-steel-plugin
extract-steel-plugin:
	+$(MAKE) -C ocaml/plugin -f extract-steel.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C extraction

.PHONY: extract-c
extract-c:
	+$(MAKE) -C c extract

.PHONY: extract
extract: extract-ocaml extract-c

.PHONY: boot
boot:
	+$(MAKE) extract
	+$(MAKE) build

.PHONY: clean-snapshot
clean-snapshot:
	rm -rf ocaml/*/generated ../include/steel/Steel_SpinLock.h
	rm -f ocaml/plugin/FStar_Parser_Parse.mly

.PHONY: full-boot
full-boot:
	+$(MAKE) build
	+$(MAKE) clean-snapshot
	+$(MAKE) boot

.PHONY: proofs
proofs:
	+$(MAKE) -C $@

.PHONY: share
share:
	+$(MAKE) -C ../share/steel

.PHONY: test
test: proofs share

.PHONY: check-for-changes
check-for-changes:
	# Test if no new files appeared
	git status ..
	test "" = "$$(git ls-files --others --exclude-standard -- ..)"
	# Test if nothing has changed
	if ! git diff-index --exit-code HEAD .. ; then git diff .. ; false ; fi

.PHONY: ci
ci:
	+$(MAKE) full-boot
	+$(MAKE) check-for-changes
	+$(MAKE) test
