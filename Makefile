all:
	coqc OneFile.v
	coqc OneFileZFC.v

test:
	python3 tests/test_basic.py
 coq_compile compile

.PHONY: all go test compile

coq_compile: coq_compile
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	python3 verify.py
	/usr/bin//usr/bin/coqc OneFileZFC.v
	/usr/bin//usr/bin/coqc tests/test_predicate_calculus.v
	/usr/bin//usr/bin/coqc tests/test_membership_fragment.v
	/usr/bin//usr/bin/coqc tests/test_isabelle_fol.v
	/usr/bin//usr/bin/coqc tests/test_isabelle_metalogic.v
	/usr/bin//usr/bin/coqc tests/test_additional_soundness.v

# go:
	python3 -m unittest discover -s tests -p 'test_*.py'
	/usr/bin//usr/bin/coqc OneFileZFC.v
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	python3 verify.py coq_compile
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	python3 verify.py
	/usr/bin//usr/bin/coqc tests/test_predicate_calculus.v
	/usr/bin//usr/bin/coqc tests/test_membership_fragment.v
	/usr/bin//usr/bin/coqc tests/test_isabelle_fol.v
	/usr/bin//usr/bin/coqc tests/test_isabelle_metalogic.v
	/usr/bin//usr/bin/coqc tests/test_additional_soundness.v

	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'

	