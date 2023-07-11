all: verify-lib verify-common verify-engine verify-l0 verify-dpe verify 

.PHONY: verify-lib
verify-lib:
	$(MAKE) -C lib verify

.PHONY: verify-common
verify-common:
	$(MAKE) -C common verify

.PHONY: verify-engine
verify-engine:
	$(MAKE) -C engine verify

.PHONY: verify-l0
verify-l0:
	$(MAKE) -C l0 verify

.PHONY: verify-dpe
verify-dpe:
	$(MAKE) -C dpe verify

# assuming share/steel/examples/pulse/dice
STEEL_HOME ?= ../../../../..
DICE_HOME ?= .

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include