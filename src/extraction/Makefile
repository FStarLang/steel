all: extract

STEEL_HOME ?= ../..

FSTAR_EXE ?= fstar.exe

OUTPUT_DIRECTORY = $(CURDIR)/../ocaml/plugin/generated
FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_BOOT_OPTIONS)

EXTRACT_FILES=ExtractSteel.ml ExtractSteelC.ml
extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(EXTRACT_FILES))

$(OUTPUT_DIRECTORY)/%.ml: %.fst
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $< \
		   --odir "$(OUTPUT_DIRECTORY)" \
		   --codegen OCaml \
		   --MLish \
		   --MLish_effect "FStarC.Effect" \
	chmod -x $@
