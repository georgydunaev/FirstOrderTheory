(* 
ocamlc -i prog.ml 
ocamlc -c prog.mli 
ocamlc -o a.out prog.ml printer.ml 
*)

let printerFm x = "ii"

let printerPrf =
  function
  | _ -> "asdfgh"
  ;;

(* | A1 of fm * fm *)

let _ =
  print_endline (printerPrf Prog.thm2)

