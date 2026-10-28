(* Basic pretty-printer for extracted Coq proofs *)

let rec print_term = function
  | FVC n -> Printf.sprintf "FVC %d" n
  | fsunion t -> Printf.sprintf "fsunion (%s)" (print_term t)
  | fspair (t1, t2) -> Printf.sprintf "fspair (%s, %s)" (print_term t1) (print_term t2)

let rec print_formula = function
  | Atom (IN (t1, t2)) -> Printf.sprintf "%s ∈ %s" (print_term t1) (print_term t2)
  | Atom (EQ (t1, t2)) -> Printf.sprintf "%s = %s" (print_term t1) (print_term t2)
  | Bot -> "⊥"
  | Conj (f1, f2) -> Printf.sprintf "(%s ∧ %s)" (print_formula f1) (print_formula f2)
  | Disj (f1, f2) -> Printf.sprintf "(%s ∨ %s)" (print_formula f1) (print_formula f2)
  | Impl (f1, f2) -> Printf.sprintf "(%s → %s)" (print_formula f1) (print_formula f2)
  | Fora (x, f) -> Printf.sprintf "∀%d. %s" x (print_formula f)
  | Exis (x, f) -> Printf.sprintf "∃%d. %s" x (print_formula f)

let print_proof proof = print_formula proof