COQBIN?=

%: Makefile.rocq

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

-include Makefile.rocq
