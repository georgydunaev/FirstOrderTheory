all:
	coqc OneFile.v
	coqc OneFileZFC.v

test:
	python3 tests/test_basic.py
 compile

.PHONY: all go test compile

coq_compile:
	coqc OneFileZFC.v
	ocamlc -c prog.ml
	ocamlc -c printer.ml
	ocamlc -o a.out prog.cmo printer.cmo
	coqc -compile OneFileZFC.v
	ocamlc -i printer.ml
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	python3 verify.py
	coqc OneFileZFC.v
	coqc tests/test_predicate_calculus.v
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v
	coqc tests/test_additional_soundness.v

# go:
	python3 -m unittest discover -s tests -p 'test_*.py'
	coqc OneFileZFC.v
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
	coqc tests/test_predicate_calculus.v
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v
	coqc tests/test_additional_soundness.v

	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'

	