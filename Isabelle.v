(* Verification of Isabelle's FOL library
1)
*)
(* use Isabelle notation in comments *)
Inductive Types : Set :=
| TVar : nat -> Types (* 'a 'b 'c ... *)
| TImp : Types -> Types -> Types (* "=>" *)
| TProp : Types (* "prop" *)
| TO : Types (* "o"=bool=object logic propositions *)
| TI : Types (* "i"=individual objects -- from ZF_base.thy *)
.

Check Types.

(* primitive Terms i.e. constants *)
Inductive PT : Set :=
| LRA : PT (* ==> : prop => prop => prop *)
| BA : PT (* !! : (a => prop) => prop *)
| TP : PT (* Trueprop : o => prop *)
| Impl : PT (* --> : [o, o] => o *)
| Fora : PT (* \forall : (i => o) => o *)
.

(* types of the primitive terms*)
Fixpoint PTT (c : PT) : Types :=
match c with
| LRA => TImp TProp (TImp TProp TProp)
| BA => TImp (TImp (TVar 0) TProp) TProp
| TP => TImp TO TI
| Impl => TImp TO (TImp TO TO)
| Fora => TImp (TImp TI TO) TO
end.

Inductive Terms : Set :=
| TVar : nat -> Terms (* x0 x1 x2 ... *)
| TCon : PT -> Terms
| TLam : nat -> Types -> Terms -> Terms
| TApp : Terms -> Terms -> Terms
.



Section Theory.
Context (A:Set) (TCons : A -> Types)
  (Adec: forall (a b:A), (a=b)\/(a<>b)).

End Theory.


Require Import Decidable PeanoNat.

Inductive Vars := | Var : nat -> Vars.

Theorem Vars_dec : forall (a b:Vars), (a=b)\/not(a=b).
Proof.
intros.
destruct a as [n], b as [m].
Search nat.
destruct (Nat.eq_dec n m) as [A|B].
auto.
right.
intro x.
apply B.
inversion x.
auto.
Qed.

(* meta and object constants *)



