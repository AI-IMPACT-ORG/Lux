# (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

COQPROJ=_CoqProject

all:
	coq_makefile -f $(COQPROJ) -o Makefile.coq
	$(MAKE) -f Makefile.coq all

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	@rm -f Makefile.coq *.d *.vo *.vos *.vok *.glob

.PHONY: all clean

