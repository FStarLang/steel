all: extract

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

# Assume FSTAR_HOME points to the F* source tree
include $(FSTAR_HOME)/.common.mk
include $(FSTAR_HOME)/ulib/gmake/z3.mk    # This pins $(Z3) ...
include $(FSTAR_HOME)/ulib/gmake/fstar.mk # and $(FSTAR) for all sub-make calls
include $(FSTAR_HOME)/src/Makefile.boot.common

OUTPUT_DIRECTORY = $(CURDIR)/../ocaml/plugin/generated
FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_BOOT_OPTIONS)

EXTRACT_FILES=ExtractSteel.ml ExtractSteelC.ml
extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(EXTRACT_FILES))

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml: %.fst
	mkdir -p $(OUTPUT_DIRECTORY)
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $< \
		   --odir "$(OUTPUT_DIRECTORY)" \
                   --codegen OCaml \
		   --MLish \
                   --extract_module $(basename $(notdir $<))
	chmod -x $@
