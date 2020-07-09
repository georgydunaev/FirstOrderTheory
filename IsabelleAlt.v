(* Every Isabelle constant has prefix I *)
(* just from IFOL.thy *)
(* Q : What's class "term"? *)

Inductive o :=
(* Should A be set or type or sth else? *)
| IFalse : o
| Iconj : o -> o -> o
| Ieq (A:Set) : A -> A -> o
(*| IAll (A:Set) : A -> A -> o*)
.

Inductive prop :=
| ITrueprop : o -> prop 
(* Isabelle's judgement == Coq's Coercion? *)
| Iimp : prop -> prop -> prop
| Iall (A:Set) : (A->prop) -> prop
.

Coercion tp := ITrueprop.

Inductive Prf : prop -> Prop :=
| Irefl : forall (A:Set) (a:A), 
   Prf (Ieq A a a)
.
