# Steel's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

# Define the Steel root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
export STEEL_HOME := $(CURDIR)
export OTHERFLAGS += --proof_recovery
include $(STEEL_HOME)/mk/common.mk

FSTAR_EXE ?= fstar.exe

all: lib verify

.PHONY: .force
.force:

plugin: plugin.src extraction.src
	cd src/ocaml && $(FSTAR_EXE) --ocamlenv dune build
	cd src/ocaml && dune install --prefix=$(STEEL_HOME)

plugin.src: .force
	$(MAKE) -f mk/plugin.mk

extraction.src: .force
	$(MAKE) -f mk/extraction.mk

.PHONY: lib
lib:
	+$(MAKE) -C src/c

.PHONY: verify-steel
verify-steel: plugin
	+$(MAKE) -C lib/steel steel

.PHONY: verify-proofs
# steelc has interfaces for modules in src/proofs, so we depend
# on them. This is not great at all since it introduces a choke point.
# It would be better to filter-out ALL_CHECKED_FILES instead.
verify-proofs: verify-steelc
	+$(MAKE) -C src/proofs

.PHONY: verify-steelc
verify-steelc: verify-steel
	+$(MAKE) -C lib/steel/c steelc

.PHONY: verify
verify: verify-steel verify-steelc
ifneq (,$(STEEL_NIGHTLY_CI))
verify: verify-proofs
endif

clean: clean_ocaml
	+$(MAKE) -C lib/steel clean ; true
	rm -rf build/plugin.checked
	rm -rf build/plugin.ml

clean_ocaml:
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel

PREFIX ?= /usr/local
override PREFIX:=$(abspath $(PREFIX))
ifeq ($(OS),Windows_NT)
  STEEL_INSTALL_PREFIX=$(shell cygpath -m $(PREFIX))
else
  STEEL_INSTALL_PREFIX=$(PREFIX)
endif
export STEEL_INSTALL_PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-ocaml install-lib install-include install-share

install-ocaml:
	cd src/ocaml && dune install --prefix=$(STEEL_INSTALL_PREFIX)

install-src-c:
	+$(MAKE) -C src/c install

install-lib:
	+$(MAKE) -C lib/steel install

install-include:
	+$(MAKE) -C include/steel install

install-share:
	+$(MAKE) -C share/steel install

install: install-ocaml install-lib install-include install-share install-src-c

.PHONY: ci
ci:
	+$(MAKE) all
	+$(MAKE) test
