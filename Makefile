all: coq_compile compile

.PHONY: all go test compile

coq_compile:
	coqc OneFileZFC.v
	coqc tests/test_predicate_calculus.v
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v

# go:
	coqc OneFileZFC.v
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	coqc tests/test_predicate_calculus.v
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v

	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'

	python3 -m unittest discover -s tests -p 'test_first_order_logic.py'
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v

	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'