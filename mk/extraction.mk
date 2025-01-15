CACHE_DIR=build/extraction.checked
OUTPUT_DIR=build/extraction.ml
CODEGEN=OCaml
SRC=src/extraction
TAG=extraction
ROOTS=$(shell find src/extraction -name '*.fst' -o -name '*.fsti')

FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --MLish --MLish_effect "FStarC.Effect"
FSTAR_OPTIONS += --with_fstarc
FSTAR_OPTIONS += --already_cached 'Prims,FStarC'

EXTRACT += --extract ExtractSteel,ExtractSteelC

include $(STEEL_HOME)/mk/boot.mk
