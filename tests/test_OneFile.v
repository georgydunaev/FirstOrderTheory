Require Import OneFile.

(* Test for Terms_ind *) Lemma test_Terms_ind : forall (t : Terms), Terms_ind (fun _ => True) (fun _ => True) (fun _ _ => True) t.
Proof.
  apply Terms_ind.
Qed.

(* Test for term_substitution *) Lemma test_term_substitution : forall (t1 t2 : Terms) (x : Var), Terms.
Proof.
  apply term_substitution.
Qed.

(* Test for term_equivalence *) Lemma test_term_equivalence : forall (t1 t2 : Terms), Terms -> Prop.
Proof.
  apply term_equivalence.
Qed.

(* Test for term_normalization *) Lemma test_term_normalization : forall (t : Terms), Terms.
Proof.
  apply term_normalization.
Qed.