# Agda Makefile
AGDA = agda
AGDAFLAGS = --compile

AGDAFILES = generated-CLEAN.agda

.PHONY: all clean check

all: $(AGDAFILES:.agda=)

check:
	$(AGDA) --check $(AGDAFILES)

clean:
	rm -f *.agdai *.hi *.o
	rm -f lib/*.agdai