(* Verification of Isabelle's FOL library
1) Maybe http://color.inria.fr/papers/koprowski06draft.pdf ?
*)
(* use Isabelle notation in comments *)
Inductive Types : Set :=
| TVar : nat -> Types (* 'a 'b 'c ... *)
| TImp : Types -> Types -> Types (* "=>" *)
| TProp : Types (* "prop" *)
| TO : Types (* "o"=bool=object logic propositions *)
| TI : Types (* "i"=individual objects -- from ZF_base.thy *)
.


Fixpoint eqTypes (a b:Types) : bool :=
match a, b with
| TVar an, TVar bn => Nat.eqb an bn
| TImp AT1 AT2, TImp BT1 BT2 => andb (eqTypes AT1 BT1) (eqTypes AT2 BT2)
| TProp, TProp => true
| TO, TO => true
| TI, TI => true
| _, _ => false
end.

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
| EVar : nat -> Terms (* x0 x1 x2 ... *)
| ECon : PT -> Terms
| ELam : nat -> Types -> Terms -> Terms
| EApp : Terms -> Terms -> Terms
.

Section Interpretation.
Context (I:nat->Types).
(*
Fixpoint TypeOfTerm (t:Terms) : Types :=
match t with
| EVar n => I n
| ECon c => PTT c
| ELam n T t => TImp T (TypeOfTerm t)
| EApp t1 t2 => ?
end.
*)

(* Inductive type has decidable equality iff
its constructors has arguments of types with decidable equality only. *)


Fixpoint TypeOfTerm (t:Terms) : option Types :=
match t with
| EVar n => Some (I n)
| ECon c => Some (PTT c)
| ELam n T t => 
  match (TypeOfTerm t) with
  | Some T2 => Some (TImp T T2)
  | None => None
  end
| EApp t1 t2 =>
  match (TypeOfTerm t1) with
  | Some T1 =>
    match T1 with
    | TImp TA TB =>
      match (TypeOfTerm t2) with
      | Some T2 => if eqTypes T2 TA then Some TB else None
      | _ => None
      end
    | _ => None
    end
  | None => None
  end
end.
End Interpretation.

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



