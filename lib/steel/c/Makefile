STEEL_ROOT ?= ../../..
include $(STEEL_ROOT)/mk/common.mk

all: steelc

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Steel.C,-Steel.ST.C' --include .. --load_cmxs steel
ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR_EXE ?= fstar.exe

MY_FSTAR=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

steelc: $(ALL_CHECKED_FILES)

clean:
	rm -f .depend* *.checked

.PHONY: all steelc clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-steelc install
install: install-steelc

.PHONY: %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/lib/steel/c/$<

install-steelc: $(addsuffix .install,$(wildcard *.fst *.fsti *.checked))
