Require Import Coq.Vectors.Vector.
(* This file will contain higher-order logic that is needed for Isabelle/ZF *)

Section FormalSystem.
Context (typeconstants:Set).
Context (typeval : typeconstants -> nat).

(* Notation: tau, sigma, alpha *)
Inductive Types : Set :=
| TVar : nat -> Types (* 'a 'b 'c ... *)
| TCon (tc : typeconstants) : (Vector.t Types (typeval tc)) -> Types
| TImp : Types -> Types -> Types (* "=>" *)
.

Definition idsubst : nat -> Types
 := fun (n:nat) => TVar n.

Definition dosubst (sub:nat -> Types) (T : Types) : Types
 := T. (* TODO *)

Context (termconstants : Set).
(* Context (termval : termconstants -> nat). *)

(* Notation: t, u, P, Q *)
Inductive Terms : Set :=
| EVar : nat -> Terms (* x0 x1 x2 ... *)
| ECon (tc : termconstants) (subst : nat -> Types) : Terms (* c_{[tau_n/alpha_n]} *)
| EApp : Terms -> Terms -> Terms  (* "t u" *)
| ELam : nat -> Types -> Terms -> Terms (* lambda x_n :: tau. t *)
.
(* | ECon : PT -> Terms *)

Context (proofconstants:Set).
(* Context (proofval : proofconstants -> nat). *)

(* Notation: p, q *)
Inductive Proofs : Set :=
| PVar : nat -> Proofs (* h0 h1 h2 ... *)
| PCon (tc : proofconstants) (subst : nat -> Types) : Proofs (* c_{[tau_n/alpha_n]} *)
| PApp1 : Proofs -> Terms -> Proofs  (* "p . t" *)
| PApp2 : Proofs -> Proofs -> Proofs  (* "p * t" *)
| PLam1 : nat -> Types -> Proofs -> Proofs (* llambda x_n :: T. p *)
| PLam2 : nat -> Types -> Proofs -> Proofs (* llambda h_n :: T. p *)
.


End FormalSystem.

(* OLD
Inductive Types : Set :=
| TVar : nat -> Types (* 'a 'b 'c ... *)
| TImp : Types -> Types -> Types (* "=>" *)
| TProp : Types (* "prop" *)
(* IFOL types *)
| TO : Types (* "o"=bool=object logic propositions *)
(* ZF types *)
| TI : Types (* "i"=individual objects -- from ZF_base.thy *)
.

Record Symb := {
  n : nat;
  tip : Types;
}.


(*
Definition Args : Types -> List
*)

Inductive Terms :=.

Inductive Terms :=
 |Atom (p:PSV) : (Vector.t Terms (psv p)) -> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 |Fora(x:SetVars.t)(f:Fo): Fo
 |Exis(x:SetVars.t)(f:Fo): Fo
.

Definition CheckType (t:Terms) := true.
*)
