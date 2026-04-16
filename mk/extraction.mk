CACHE_DIR=build/extraction.checked
OUTPUT_DIR=build/extraction.ml
CODEGEN=PluginNoLib
SRC=src/extraction
TAG=extraction
ROOTS=$(shell find src/extraction -name '*.fst' -o -name '*.fsti')

FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --with_fstarc
FSTAR_OPTIONS += --warn_error -272 # top-level effects
FSTAR_OPTIONS += --already_cached 'Prims,FStarC'

EXTRACT += --extract ExtractSteel,ExtractSteelC

include $(STEEL_HOME)/mk/boot.mk
