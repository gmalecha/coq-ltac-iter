all: Makefile.coq
	@ $(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@ $(MAKE) -f Makefile.coq clean
	@ rm Makefile.coq

install: all
	@ $(MAKE) -f Makefile.coq install

Makefile.coq: arguments.txt Makefile
	@ coq_makefile -f arguments.txt -o Makefile.coq