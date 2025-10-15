# Coq Makefile
COQC = coqc
COQFLAGS = -Q lib lib

VFILES = lib/generated_Core.v lib/generated_Observers.v lib/generated_Kernels.v lib/generated_NormalForms.v generated_CLEAN.v

.PHONY: all clean

all: $(VFILES:.v=.vo)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f *.vo *.glob *.vok *.vos
	rm -f lib/*.vo lib/*.glob lib/*.vok lib/*.vos