# NOTE: I would have preferred to separate the cache dir
# into something like build/plugin.checked, but this
# means every client now has to point there too, and we have
# to install that directory. So I'm just placing them in lib/steel
# as the Makefile there does. This should be fine really.
CACHE_DIR=lib/steel

OUTPUT_DIR=build/plugin.ml
CODEGEN=Plugin
SRC=lib/steel
TAG=plugin
ROOTS=Steel.Effect.Common.fst Steel.ST.GenElim.Base.fst Steel.ST.GenElim1.Base.fst
EXTRACT=--extract '+Steel.Effect.Common +Steel.ST.GenElim.Base +Steel.ST.GenElim1.Base'

include $(STEEL_HOME)/mk/boot.mk
