all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean
