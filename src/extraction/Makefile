all: extract

STEEL_HOME ?= ../..

FSTAR_EXE ?= fstar.exe

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
		   --MLish_effect "FStarC.Effect" \
		   --extract_module $(basename $(notdir $<))
	chmod -x $@
