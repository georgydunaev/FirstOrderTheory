(* === AUTONOMOUS WORKER PROVENANCE DECLARATION === 
* You are: 'mistral/codestral-latest' (Capability Tier 1, Verified Win Rate: 94.5%). 
* You are working in repository 'FirstOrderTheory' in /botworkspace/FirstOrderTheory. 
* In all commits, pull requests, and file headers, you must honestly declare your model identity ('mistral/codestral-latest') and capability tier (1). 
* 
* Goal: Resolve and verify Ticket: [Curated] Ticket 003: Improve Isabelle's FOL Library 
* Ticket Reference: /botworkspace/FirstOrderTheory/tickets/ticket_003.md 
*)

(* Implementation of Isabelle's FOL Library *)

(* Basic Definitions *)

(* Terms *)

type variable = string

type constant = string

type term = Var of variable | Const of constant | Func of constant * term list

let rec term_to_string = function
    | Var v -> v
    | Const c -> c
    | Func (f, args) -> f ^ "(" ^ String.concat ", " (List.map term_to_string args) ^ ")"

(* Formulas *)

type formula = True | False | Atom of term | Not of formula | And of formula * formula | Or of formula * formula | Implies of formula * formula | Iff of formula * formula | Forall of variable * formula | Exists of variable * formula

let rec formula_to_string = function
    | True -> "True"
    | False -> "False"
    | Atom t -> term_to_string t
    | Not f -> "¬" ^ formula_to_string f
    | And (f1, f2) -> "(" ^ formula_to_string f1 ^ " ∧ " ^ formula_to_string f2 ^ ")"
    | Or (f1, f2) -> "(" ^ formula_to_string f1 ^ " ∨ " ^ formula_to_string f2 ^ ")"
    | Implies (f1, f2) -> "(" ^ formula_to_string f1 ^ " → " ^ formula_to_string f2 ^ ")"
    | Iff (f1, f2) -> "(" ^ formula_to_string f1 ^ " ↔ " ^ formula_to_string f2 ^ ")"
    | Forall (v, f) -> "∀" ^ v ^ ". " ^ formula_to_string f
    | Exists (v, f) -> "∃" ^ v ^ ". " ^ formula_to_string f

(* Inference Rules *)

let modus_ponens (f1, f2) = match (f1, f2) with
    | (Implies (f, g), f') when f = f' -> g
    | _ -> raise (Failure "Modus Ponens failed")

let universal_instantiation (v, t, f) = match f with
    | Forall (v', f') when v = v' -> substitute_term v t f'
    | _ -> raise (Failure "Universal Instantiation failed")

and substitute_term v t = function
    | Atom (Var v') when v = v' -> Atom t
    | Atom (Func (c, args)) -> Atom (Func (c, List.map (substitute_term v t) args))
    | Not f -> Not (substitute_term v t f)
    | And (f1, f2) -> And (substitute_term v t f1, substitute_term v t f2)
    | Or (f1, f2) -> Or (substitute_term v t f1, substitute_term v t f2)
    | Implies (f1, f2) -> Implies (substitute_term v t f1, substitute_term v t f2)
    | Iff (f1, f2) -> Iff (substitute_term v t f1, substitute_term v t f2)
    | Forall (v', f') when v = v' -> Forall (v', f')
    | Forall (v', f') -> Forall (v', substitute_term v t f')
    | Exists (v', f') when v = v' -> Exists (v', f')
    | Exists (v', f') -> Exists (v', substitute_term v t f')
    | _ as f -> f