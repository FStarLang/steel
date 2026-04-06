all: verify test

KRML_EXE ?= krml
KRMLLIB := $(shell $(KRML_EXE) -locate-krmllib)
KRMLINC := $(shell $(KRML_EXE) -locate-include)

# assuming share/steel/examples/steelc
STEEL_HOME ?= ../../../..

FSTAR_OPTIONS += --include $(STEEL_HOME)/lib/steel/c --warn_error @250
FSTAR_OPTIONS += --ext compat:open_metas

FSTAR_OPTIONS += --include $(KRMLLIB)

FSTAR_DEP_OPTIONS += --extract krml:*,-FStar.List,-FStar.Tactics,-LowStar.Monotonic.Buffer

include $(STEEL_HOME)/share/steel/Makefile.include

# NOTE: this is NOT a phony rule
extract: $(ALL_KRML_FILES)
	$(KRML_EXE) -warn-error @4-26 -skip-compilation -skip-makefiles -bundle 'FStar.\*,Steel.\*,C' $^
	touch $@

ALL_MODULE_NAMES=$(basename $(wildcard *.fst))
ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))

$(ALL_C_FILES): %.c: extract
	test -f $@
	touch $@

ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRMLINC) -I $(KRMLLIB)/dist/minimal -I $(STEEL_HOME)/include/steel -o $@ -c $<

test: $(ALL_O_FILES)

clean::
	rm -f *.c *.h *.o extract

.PHONY: test
