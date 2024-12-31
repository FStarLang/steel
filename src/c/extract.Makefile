all: world

LIB_STEEL=../../lib/steel
INCLUDE_STEEL=../../include/steel

world: $(INCLUDE_STEEL)/Steel_SpinLock.h

STEEL_HOME ?= ../..
include $(STEEL_HOME)/mk/locate_fstar.mk

FSTAR = $(RUNLIM) $(FSTAR_EXE) --cache_checked_modules \
  --include $(LIB_STEEL) \
  --load_cmxs steel \
  --warn_error @241 \
  --cmi \
  --already_cached '*,'

ROOTS = $(LIB_STEEL)/Steel.SpinLock.fsti

.depend: $(ROOTS)
	$(FSTAR) $(OTHERFLAGS) --extract '* -FStar.Stubs' --dep full $(ROOTS) > $@.tmp
	mv $@.tmp $@

include .depend

%.krml: | .depend
	$(FSTAR) $(OTHERFLAGS) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

KRML=$(KRML_HOME)/krml

$(INCLUDE_STEEL)/Steel_SpinLock.h: $(ALL_KRML_FILES)
	$(KRML) \
	  -fparentheses \
	  -fcurly-braces \
	  -fno-shadow \
	  -header copyright-header.txt \
	  -minimal \
	  -skip-compilation \
	  -tmpdir $(dir $@) \
	  -skip-makefiles \
	  -extract-uints \
	  $(addprefix -add-include ,'<stdbool.h>' '"steel_types.h"') \
	  -bundle Steel.SpinLock=Steel.*,Prims,FStar.*,LowStar.* \
	  $^
	chmod -x $@
