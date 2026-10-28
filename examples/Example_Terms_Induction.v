(* Example: Using the Terms_ind theorem to prove a property about terms in first-order logic. *)

Require Import OneFile.

(* Define a property T for terms. For this example, we will use a simple property that holds for all terms. *)
Definition T (t:Terms) : Prop := True.

(* Define the hypotheses for the Terms_ind theorem. *)
Definition H_FVC (sv:SV) : T (FVC sv) := True.
Definition H_FSC (f:FSV) (v:Vector.t Terms (fsv f)) (H_args: forall i, T (Vector.nth v i)) : T (FSC f v) := True.

(* Use the Terms_ind theorem to prove that T holds for any term t. *)
Theorem Example_Terms_Induction : forall (t:Terms), T t.
Proof.
  apply Terms_ind.
  exact H_FVC.
  exact H_FSC.
Qed.
