(* This file is manually created based on the extracted Coq definitions *)

(* SetVars represents set variables. *)
type set_vars = Va of int

(* Terms represents terms, including free variables, union, and pairing. *)
type terms =
  | FVC of set_vars
  | Fsunion of terms
  | Fspair of terms * terms

(* AtomFm represents atomic formulas, including membership and equality. *)
type atom_fm =
  | IN of terms * terms
  | EQ of terms * terms

(* Fm represents formulas, including atomic formulas, conjunction, disjunction, implication, and quantifiers. *)
type fm =
  | Atom of atom_fm
  | Bot
  | Conj of fm * fm
  | Disj of fm * fm
  | Impl of fm * fm
  | Fora of set_vars * fm
  | Exis of set_vars * fm

(* X represents ordinals. *)
type x = Ord of int

(* In represents the membership relation between two ordinals. *)
let in_relation x1 x2 =
  match x1, x2 with
  | Ord n1, Ord n2 -> n1 < n2

(* membership_model represents the model of finite ordinals with transitive-closure membership. *)
let membership_model = "Finite ordinals with transitive-closure membership"

(* union_axiom represents the union axiom. *)
let union_axiom x y = failwith "Axiom not implemented"

(* pairing_axiom represents the pairing axiom. *)
let pairing_axiom x y = failwith "Axiom not implemented"

(* equality_axiom represents the equality axiom. *)
let equality_axiom x y = failwith "Axiom not implemented"

(* zf_fragment_validated represents the validated fragment of ZF set theory. *)
let zf_fragment_validated = "Ordinal hierarchy"
