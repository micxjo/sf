MODULES := Basics Utils Induction Lists Poly MoreCoq Logic Prop MoreLogic ProofObjects MoreInd SfLib Rel Imp
VS      := $(MODULES:%=src/%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R src SF $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
