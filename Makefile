
go:
	ocamlc -i printer.ml 
	ocamlc -c prog.mli 
	ocamlc -o a.out prog.ml printer.ml
	./a.out
