(* === AUTONOMOUS WORKER PROVENANCE DECLARATION === 
* You are: 'mistral/codestral-latest' (Capability Tier 1, Verified Win Rate: 94.5%). 
* You are working in repository 'FirstOrderTheory' in /botworkspace/FirstOrderTheory. 
* In all commits, pull requests, and file headers, you must honestly declare your model identity ('mistral/codestral-latest') and capability tier (1). 
* 
* Goal: Resolve and verify Ticket: [Curated] Ticket 003: Improve Isabelle's FOL Library 
* Ticket Reference: /botworkspace/FirstOrderTheory/tickets/ticket_003.md 
*)

(* Test Suite for Isabelle's FOL Library *)

(* Test Terms *)

let test_terms () =
    let v = Var "x"
    let c = Const "P"
    let f = Func ("f", [v; c])
    assert (term_to_string v = "x");
    assert (term_to_string c = "P");
    assert (term_to_string f = "f(x, P)")

(* Test Formulas *)

let test_formulas () =
    let t = Atom (Var "x")
    let f = Not t
    let g = And (t, f)
    let h = Forall ("x", g)
    assert (formula_to_string t = "x");
    assert (formula_to_string f = "¬x");
    assert (formula_to_string g = "(x ∧ ¬x)");
    assert (formula_to_string h = "∀x. (x ∧ ¬x)")

(* Test Inference Rules *)

let test_inference_rules () =
    let f1 = Implies (Atom (Var "x"), Atom (Var "y"))
    let f2 = Atom (Var "x")
    let f3 = modus_ponens (f1, f2)
    assert (formula_to_string f3 = "y");
    let f4 = Forall ("x", Atom (Var "x"))
    let f5 = universal_instantiation ("x", Const "a", f4)
    assert (formula_to_string f5 = "a")

(* Run Tests *)

let _ =
    test_terms ();
    test_formulas ();
    test_inference_rules ()