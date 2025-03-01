all: steelc

# assuming src/proofs/steelc
STEEL_HOME=../../..
include $(STEEL_HOME)/mk/common.mk
.DEFAULT_GOAL := all

FSTAR_EXE ?= fstar.exe

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Steel.C,-Steel.ST.C,+Steel.ST.C.Types.Array.Base' --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c
FSTAR_OPTIONS+=--ext context_pruning
FSTAR_OPTIONS+=--compat_pre_typed_indexed_effects
FSTAR_OPTIONS+=--use_hints
FSTAR_OPTIONS+=--cache_dir _cache
FSTAR_OPTIONS+=--load_cmxs steel
ifeq ($(ADMIT),1)
FSTAR_OPTIONS+=--admit_smt_queries true
endif

MY_FSTAR=$(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(MY_FSTAR) $(SIL) $<

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(MY_FSTAR) --dep full @$@.rsp --output_deps_to $@

include .depend

steelc: $(ALL_CHECKED_FILES)

clean:
	rm -f .depend* *.checked

.PHONY: all steelc clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
