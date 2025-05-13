COQMFFLAGS := -Q . LF  

ALLVFILES := Basics.v Induction.v Lists.v Poly.v Tactics.v Logic.v IndProp.v Maps.v ProofObjects.v IndPrinciples.v Rel.v Imp.v ImpParser.v ImpCEvalFun.v Auto.v AltAuto.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
