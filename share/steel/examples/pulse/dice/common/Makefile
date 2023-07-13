all: verify

# assuming share/steel/examples/pulse/dice/l0
STEEL_HOME ?= ../../../../../..
DICE_HOME ?= ../

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse --include $(DICE_HOME)/lib --include $(DICE_HOME)/engine --include $(DICE_HOME)/l0

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
