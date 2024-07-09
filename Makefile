LIBNAME=Repl

all:
	{ echo "-R . $(LIBNAME) " ; ls *.v ; } > _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
	make -f CoqMakefile

clean:
	rm -f *.aux *.glob *.vo *.vok *.vos
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d _CoqProject