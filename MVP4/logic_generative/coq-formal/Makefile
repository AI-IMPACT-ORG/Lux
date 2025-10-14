# (c) 2025 AI.IMPACT GmbH

COQPROJ=_CoqProject

all:
	coq_makefile -f $(COQPROJ) -o Makefile.coq
	$(MAKE) -f Makefile.coq all

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	@rm -f Makefile.coq *.d *.vo *.vos *.vok *.glob

.PHONY: all clean

