# Lean Makefile
LEAN = lean
LEANFLAGS = --check

LEANFILES = generated-CLEAN.lean lib/generated-Core.lean lib/generated-Observers.lean lib/generated-Kernels.lean lib/generated-NormalForms.lean

.PHONY: all clean check

all: check

check:
	$(LEAN) $(LEANFLAGS) $(LEANFILES)

clean:
	rm -f *.olean
	rm -f lib/*.olean