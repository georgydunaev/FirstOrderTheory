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
Iimpl (Iimpl A (Iimpl B C)) (Iimpl (Iimpl A B) (Iimpl A C))
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

Inductive PrfCtx (G : prop -> Type): prop -> Type :=
| ctx p : PrfCtx G p
| ax p : Prf p -> PrfCtx G p
.

(*
Inductive WithMP (G : prop -> Type): prop -> Type :=
| Imp : forall (P Q : o),
   WithMP (Iimp P Q) -> WithMP P -> WithMP Q
*)




Theorem Deduction (P Q:prop) (H : Prf P -> Prf Q)
:  Prf (Iimpl P Q).
Proof.
Abort.
(*
Context (P:prop).
Check A2 P P P.*)

(* The following is useful when one does not use context:
(as it possibly done in Isabelle) *)
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
refine (MP _ _ _).
refine (MP _ _ _ _).
refine (A2 _ _ _).
refine (dropL _ _ _).
refine (A1 _ _).
Defined.

(* Simple theorems: *)
Definition ITrue : o := Iimp IFalse IFalse. 
Theorem TrueI: Prf ITrue.
Proof.
unfold ITrue.
apply IimpI.
apply assu.
Defined.
(*--------------------------*)
(* What if "inductive extension"? *)
(*
Axiom elems : forall A:Type, A -> Type.
*)


Inductive bigunion {A} (f:A -> Type) : Type :=
| c : forall n : A, f n -> bigunion f
. (* exists *)

(*| z : f 0 -> bigunion
| s : forall n : nat,  *)

Fixpoint q (n:nat) :=
