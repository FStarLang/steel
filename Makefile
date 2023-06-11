# Steel's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

all: lib verify

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    _fstar_home := $(realpath $(dir $(_check_fstar))/..)
    ifeq ($(OS),Windows_NT)
      OCAMLPATH := $(shell cygpath -m $(_fstar_home)/lib);$(OCAMLPATH)
    else
      OCAMLPATH := $(_fstar_home)/lib:$(OCAMLPATH)
    endif
  endif
else
  _fstar_home := $(FSTAR_HOME)
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif

# Define the Steel root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  STEEL_HOME := $(shell cygpath -m $(CURDIR))
else
  STEEL_HOME := $(CURDIR)
endif

.PHONY: ocaml
ocaml:
	cd src/ocaml && dune build
	cd src/ocaml && dune install --prefix=$(STEEL_HOME)

.PHONY: lib
lib:
	+$(MAKE) -C src/c

.PHONY: verify-steel
verify-steel: ocaml
	+$(MAKE) -C lib/steel steel

.PHONY: verify-pulse
verify-pulse: verify-steel
	+$(MAKE) -C lib/steel/pulse pulse

.PHONY: verify-steelc
verify-steelc: verify-steel
	+$(MAKE) -C lib/steel/c steelc

.PHONY: verify
verify: verify-steel verify-pulse verify-steelc

clean: clean_ocaml
	+$(MAKE) -C lib/steel clean ; true

clean_ocaml:
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel

PREFIX ?= /usr/local
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


.PHONY: reboot-steel
reboot-steel:
	+$(MAKE) -C lib/steel steel STEEL_BOOT=1
	rm -f src/ocaml/plugin/.depend-steel
	+$(MAKE) -C src/ocaml/plugin/ -f extract-steel.Makefile .depend-steel STEEL_BOOT=1
	+$(MAKE) -C src/ocaml/plugin/ -f extract-steel.Makefile STEEL_BOOT=1
	@echo The steel files were extracted.
