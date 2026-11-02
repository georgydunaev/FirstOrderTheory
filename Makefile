.PHONY: all go test compile coq_compile

all:
	coqc OneFile.v
	coqc OneFileZFC.v

test:
	python3 -m unittest discover -s tests -p 'test_*.py'

go:
	coqc OneFileZFC.v
	ocamlc -i printer.ml
	ocamlc -c prog.mli
	ocamlc -o a.out prog.ml printer.ml
	./a.out

compile:
	python3 verify.py
	python3 -m unittest discover -s tests -p 'test_*.py'

coq_compile:
	coqc OneFileZFC.v
	ocamlc -c prog.ml
	ocamlc -c printer.ml
	ocamlc -o a.out prog.cmo printer.cmo
	./a.out
