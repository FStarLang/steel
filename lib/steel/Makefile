STEEL_ROOT ?= ../..
include $(STEEL_ROOT)/mk/common.mk

all: steel steelc

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Steel' --load_cmxs steel
ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR_EXE ?= fstar.exe

COMPAT_INDEXED_EFFECTS=--compat_pre_typed_indexed_effects
MY_FSTAR=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

include runlim.mk

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

# These modules already verify without the flag.
Steel.ST.GhostPCMReference.fst.checked: COMPAT_INDEXED_EFFECTS=
Steel.Semantics.Hoare.MST.fst.checked: OTHERFLAGS+=--ext 'compat:injectivity'
Steel.ST.EphemeralHashtbl.fst.checked: OTHERFLAGS+=--ext 'compat:injectivity'

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

steel: $(ALL_CHECKED_FILES)

.PHONY: steelc
steelc: steel
	+$(MAKE) -C c

clean:
	rm -f .depend* *.checked */.depend* */*.checked

.PHONY: all steel clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-steel install-steelc install
install: install-steel install-steelc

install-steelc:
	+$(MAKE) -C c install

.PHONY: %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/lib/steel/$<

install-steel: $(addsuffix .install,$(wildcard *.fst *.fsti *.checked) libsteel.a)
