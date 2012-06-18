!INCLUDE Makefile.common

COQFLAGS=-coqlib "$(COQLIB)" 
COQC=coqc

all: $(TARGETS)

clean:
	del /S *.vo *.dep *.glob

.SUFFIXES: .v .vo .dep

.v.vo:
	$(COQC) -dont-load-proofs $*

Makefile.deps: $(TARGETS:.vo=.dep)
	type $** > $@ 2>NUL

.v.dep:
	coqdep -I . $< > $@

!IF EXIST (Makefile.deps)
!INCLUDE Makefile.deps
!ENDIF

