# define COQBIN to the empty string if it's not already defined
# (in case we want to run make with --warn-undefined-variables)
COQBIN?=

# all unknown targets depend on the generated Rocq makefile
%: Makefile.rocq

# rule to generate the Rocq makefile
Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

# use the generated Rocq makefile
# -include instead of include: don't error if it's not there
# (IIRC some version of make doesn't realize that it should be built if we don't use -include)
-include Makefile.rocq
