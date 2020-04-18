(* Verification of Isabelle
1)
*)

Inductive Types : Set :=
| TVar : nat -> Types
| TImp : Types -> Types -> Types
| TProp : Types
| TO : Types (* bool=object logic propositions *)
| TI : Types (* individual objects *)
.

Check Types.

(* meta and object constants *)
Inductive MC : Set :=
| LRA : MC (* ==> : prop => prop => prop *)
| BA : MC (* !! : (a => prop) => prop *)
| TP : MC (* Trueprop : o => prop *)
| Impl : MC (* --> : [o, o] => o *)
| Fora : MC (* \forall : (i => o) => o *)
.

(* metaconstants' types*)
Fixpoint MCT (c : MC) : Types :=
match c with
| LRA => TImp TProp (TImp TProp TProp)
| BA => TImp (TImp (TVar 0) TProp) TProp
| TP => TImp TO TI
| Impl => TImp TO (TImp TO TO)
| Fora => TImp (TImp TI TO) TO
end.

Inductive Terms : Set :=
| MVar : nat -> Terms
| MCon : MC -> Terms
| MLam : nat -> Types -> Terms -> Terms
| MApp : Terms -> Terms -> Terms
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




