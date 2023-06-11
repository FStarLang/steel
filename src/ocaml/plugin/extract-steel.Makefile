all: extract

LIB_STEEL=$(CURDIR)/../../../lib/steel
OUTPUT_DIRECTORY=generated

CODEGEN = Plugin

ifneq (,$(FSTAR_HOME))
	FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
	FSTAR=fstar.exe
endif

PLUGIN_ROOTS+= Steel.Effect.Common.fsti
PLUGIN_ROOTS+= Steel.ST.GenElim.Base.fsti
PLUGIN_ROOTS+= Steel.ST.GenElim1.Base.fsti
FSTAR_FILES:=$(addprefix $(LIB_STEEL)/, $(PLUGIN_ROOTS))

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(OTHERFLAGS) --include $(LIB_STEEL) --cache_checked_modules --odir $(OUTPUT_DIRECTORY) --warn_error @241
MY_FSTAR+=$(if $(STEEL_BOOT),, --already_cached '*,')

EXTRACT_MODULES=--extract '+Steel.Effect.Common +Steel.ST.GenElim.Base +Steel.ST.GenElim1.Base'

COMPAT_INDEXED_EFFECTS=--compat_pre_typed_indexed_effects

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<

# And then, in a separate invocation, from each .checked we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))
	chmod -x $@

.depend-steel: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full $(EXTRACT_MODULES) $(addprefix --include , $(INCLUDE_PATHS)) @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend-steel

extract: $(ALL_ML_FILES)

.PHONY: all extract
