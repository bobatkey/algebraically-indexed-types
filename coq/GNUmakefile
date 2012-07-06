include Makefile.common

COQFLAGS=-coqlib "$(COQLIB)" 
COQC=coqc

all: $(TARGETS)

clean:
	rm -f *.vo *.dep *.glob

.SUFFIXES: .v .vo .dep

.v.vo:
	$(COQC) -dont-load-proofs $*

Makefile.deps: $(TARGETS:.vo=.dep)
	cat $^ > $@ 2>/dev/null

.v.dep:
	coqdep -I . $< > $@

-include Makefile.deps

