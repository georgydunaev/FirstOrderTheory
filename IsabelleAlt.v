(* Every Isabelle constant has prefix I *)
(* just from IFOL.thy *)
(* Q : What's class "term"? *)

(* Should A be set or type or sth else? *)
Notation tip := Set.

(* TODO: Define "Pointed set" type...
Inductive PSet :=
| C (S:Set) (s:S) : PSet *)

Inductive o :=
(* Equality *)
| Ieq (A:tip) : A -> A -> o
(* Propositional logic *)
| IFalse : o
| Iconj : o -> o -> o
| Iimp : o -> o -> o
(*| IAll (A:tip) : A -> A -> o*)
.

Inductive prop :=
| ITrueprop : o -> prop 
| Iimpl : prop -> prop -> prop
| Iall (A:tip) : (A->prop) -> prop
.

(* Isabelle's judgement == Coq's Coercion? *)
Coercion tp := ITrueprop.

(* TODO: add context! *)
Inductive Prf : prop -> Type :=
(* Metalogic *)
| A1 A B :  Prf (Iimpl A (Iimpl B A))
| A2 A B C :  Prf (
Iimpl (Iimpl A (Iimpl B C))
(Iimpl (Iimpl A B) (Iimpl A C))
)
| MP A B : Prf (Iimpl A B) -> Prf A -> Prf B
(* |  assu P : Prf (Iimpl P P) *)
(* Object logic *)
(* Equality *)
| Irefl : forall (A:tip) (a:A),
   Prf (Ieq A a a)
| Isubst : forall (A:tip) (a b:A) (P:A -> o),
   Prf (Ieq A a b) -> Prf (P a) -> Prf (P b)
(* Propositional logic *)
| IimpI : forall (P Q : o),
   Prf (Iimpl P Q) -> Prf (Iimp P Q)
| Imp : forall (P Q : o),
   Prf (Iimp P Q) -> Prf P -> Prf Q
.

Theorem Deduction (P Q:prop) (H : Prf P -> Prf Q)
:  Prf (Iimpl P Q).
Proof.
Abort.
(*
Context (P:prop).
Check A2 P P P.*)

Theorem assu P : Prf (Iimpl P P).
Proof.
refine (MP _ _ _ _).
refine (MP _ _ _ _).
refine (A2 P (Iimpl P P) P).
refine (A1 _ _).
refine (A1 _ _).
Defined.

Theorem dropL P Q : Prf Q -> Prf (Iimpl P Q).
Proof.
intro H.
refine (MP _ _ _ _).
refine (A1 _ _).
assumption.
Defined.

Theorem dropR P Q R : Prf (Iimpl P R) 
 -> Prf (Iimpl P (Iimpl Q R)).
Proof.
intro H.
Defined.

Definition ITrue : o := Iimp IFalse IFalse. 
Theorem TrueI: Prf ITrue.
unfold ITrue.
apply IimpI.

refine (IimpI _ _ ).
