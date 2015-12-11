all: Makefile.coq
	@ $(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@ $(MAKE) -f Makefile.coq clean
	@ rm Makefile.coq

install: all
	@ $(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject Makefile
	@ coq_makefile -f _CoqProject -o Makefile.coq
