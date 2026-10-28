all: compile

.PHONY: all go test compile

# go:
	echo 'Coq compiler not found'
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

# compile:
	coqc tests/test_predicate_calculus.v
	coqc tests/test_membership_fragment.v
	coqc tests/test_isabelle_fol.v
	coqc tests/test_isabelle_metalogic.v
	echo 'Coq compiler not found'
	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'
	echo 'Coq compiler not found'

# Structural regression tests: need only Python 3 (no Coq required).
# Author: opencode/mimo-v2.6-flash-free (Capability Tier 1) - ticket #7231
test:
	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'
	python3 -m unittest discover -s tests -p 'test_first_order_logic.py'
test:
	python3 -m unittest discover -s tests -p 'test_*.py'
	python3 -m unittest discover -s tests -p 'test_additional.py'