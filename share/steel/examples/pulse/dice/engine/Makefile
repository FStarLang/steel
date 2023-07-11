all: verify

# assuming share/steel/examples/pulse/dice/engine
STEEL_HOME ?= ../../../../../..
DICE_HOME ?= ../

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse --include $(DICE_HOME)/lib --include $(DICE_HOME)/common

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
