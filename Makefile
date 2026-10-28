all: compile test

.PHONY: all go test compile

go:
	coqc Isabelle.v
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

compile:
	coqc Isabelle.v
	python3 -m unittest discover -s tests -p 'test_*.py'
	coqc Isabelle.v

# Structural regression tests: need only Python 3 (no Coq required).
# Author: opencode/mimo-v2.6-flash-free (Capability Tier 1) - ticket #7231
test:
	python3 -m unittest discover -s tests -p 'test_*.py'