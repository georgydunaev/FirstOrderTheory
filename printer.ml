(* Pretty-printer for extracted proof constructors *)

let rec print_term = function
  | FVC n -> Printf.printf "FVC %d" n
  | fsunion t -> Printf.printf "fsunion (%a)" print_term t
  | fspair t1 t2 -> Printf.printf "fspair (%a, %a)" print_term t1 print_term t2

let rec print_atomfm = function
  | IN (t1, t2) -> Printf.printf "IN (%a, %a)" print_term t1 print_term t2
  | EQ (t1, t2) -> Printf.printf "EQ (%a, %a)" print_term t1 print_term t2

let rec print_fm = function
  | Atom af -> print_atomfm af
  | Bot -> Printf.printf "Bot"
  | Conj (f1, f2) -> Printf.printf "Conj (%a, %a)" print_fm f1 print_fm f2
  | Disj (f1, f2) -> Printf.printf "Disj (%a, %a)" print_fm f1 print_fm f2
  | Impl (f1, f2) -> Printf.printf "Impl (%a, %a)" print_fm f1 print_fm f2
  | Fora (x, f) -> Printf.printf "Fora (%d, %a)" x print_fm f
  | Exis (x, f) -> Printf.printf "Exis (%d, %a)" x print_fm f

let print_x = function
  | Ord n -> Printf.printf "Ord %d" n
