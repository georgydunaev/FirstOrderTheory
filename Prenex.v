(* Author: First-Order Deduction and Meta-Theorems Specialist *)
(* Module Prenex: Formalization of Prenex Normal Form, Quantifier Duality, *)
(* Quantifier Shifting Laws, Deduction Theorem, and Skolem Equisatisfiability. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** SECTION 1: SYNTAX OF FIRST-ORDER LOGIC **)

Inductive term : Type :=
| Var : nat -> term
| Func : nat -> list term -> term.

Inductive formula : Type :=
| FAtom : nat -> list term -> formula
| FBot : formula
| FConj : formula -> formula -> formula
| FDisj : formula -> formula -> formula
| FImpl : formula -> formula -> formula
| FForall : nat -> formula -> formula
| FExists : nat -> formula -> formula.

Definition FNeg (phi : formula) : formula := FImpl phi FBot.
Definition FTop : formula := FNeg FBot.
Definition FIff (phi psi : formula) : formula := FConj (FImpl phi psi) (FImpl psi phi).

Fixpoint free_in_term (x : nat) (t : term) : bool :=
  match t with
  | Var y => Nat.eqb x y
  | Func _ ts => existsb (free_in_term x) ts
  end.

Fixpoint free_in (x : nat) (phi : formula) : bool :=
  match phi with
  | FAtom _ ts => existsb (free_in_term x) ts
  | FBot => false
  | FConj phi1 phi2 | FDisj phi1 phi2 | FImpl phi1 phi2 =>
      free_in x phi1 || free_in x phi2
  | FForall y phi1 | FExists y phi1 =>
      if Nat.eqb x y then false else free_in x phi1
  end.

Fixpoint subst_term (s : term) (x : nat) (t : term) : term :=
  match t with
  | Var y => if Nat.eqb y x then s else Var y
  | Func f ts => Func f (map (subst_term s x) ts)
  end.

Fixpoint subst_form (s : term) (x : nat) (phi : formula) : formula :=
  match phi with
  | FAtom p ts => FAtom p (map (subst_term s x) ts)
  | FBot => FBot
  | FConj phi1 phi2 => FConj (subst_form s x phi1) (subst_form s x phi2)
  | FDisj phi1 phi2 => FDisj (subst_form s x phi1) (subst_form s x phi2)
  | FImpl phi1 phi2 => FImpl (subst_form s x phi1) (subst_form s x phi2)
  | FForall y phi1 => if Nat.eqb y x then FForall y phi1 else FForall y (subst_form s x phi1)
  | FExists y phi1 => if Nat.eqb y x then FExists y phi1 else FExists y (subst_form s x phi1)
  end.

(** SECTION 2: SEMANTICS AND MODEL THEORY **)

Record Model := {
  D : Type;
  d0 : D;
  I_f : nat -> list D -> D;
  I_p : nat -> list D -> Prop
}.

Definition cng {D : Type} (val : nat -> D) (x : nat) (d : D) : nat -> D :=
  fun y => if Nat.eqb y x then d else val y.

Fixpoint eval_term (M : Model) (val : nat -> D M) (t : term) : D M :=
  match t with
  | Var x => val x
  | Func f ts => (I_f M) f (map (eval_term M val) ts)
  end.

Fixpoint eval_form (M : Model) (val : nat -> D M) (phi : formula) : Prop :=
  match phi with
  | FAtom p ts => (I_p M) p (map (eval_term M val) ts)
  | FBot => False
  | FConj phi1 phi2 => eval_form M val phi1 /\ eval_form M val phi2
  | FDisj phi1 phi2 => eval_form M val phi1 \/ eval_form M val phi2
  | FImpl phi1 phi2 => eval_form M val phi1 -> eval_form M val phi2
  | FForall x phi1 => forall d : D M, eval_form M (cng val x d) phi1
  | FExists x phi1 => exists d : D M, eval_form M (cng val x d) phi1
  end.

Definition sem_valid (phi : formula) : Prop :=
  forall (M : Model) (val : nat -> D M), eval_form M val phi.

Definition sem_equiv (phi psi : formula) : Prop :=
  forall (M : Model) (val : nat -> D M), eval_form M val phi <-> eval_form M val psi.

Definition sem_impl (phi psi : formula) : Prop :=
  forall (M : Model) (val : nat -> D M), eval_form M val phi -> eval_form M val psi.

Definition not_free_in (x : nat) (psi : formula) : Prop :=
  forall (M : Model) (val : nat -> D M) (d : D M),
    eval_form M (cng val x d) psi <-> eval_form M val psi.

Definition satisfiable (phi : formula) : Prop :=
  exists (M : Model) (val : nat -> D M), eval_form M val phi.

(** SECTION 3: QUANTIFIER DUALITY THEOREMS **)

Theorem not_exists_iff_forall_not : forall x phi,
  sem_equiv (FNeg (FExists x phi)) (FForall x (FNeg phi)).
Proof.
  intros x phi M val.
  split.
  - intros Hnex d Hphi.
    apply Hnex. exists d. exact Hphi.
  - intros Hnot [d Hphi].
    exact (Hnot d Hphi).
Qed.

Theorem exists_not_implies_not_forall : forall x phi,
  sem_impl (FExists x (FNeg phi)) (FNeg (FForall x phi)).
Proof.
  intros x phi M val [d Hnotphi] Hall.
  apply Hnotphi.
  apply (Hall d).
Qed.

Section ClassicalDuality.
Variable LEM : forall P : Prop, P \/ ~ P.

Theorem classical_not_forall_iff_exists_not : forall x phi,
  sem_equiv (FNeg (FForall x phi)) (FExists x (FNeg phi)).
Proof.
  intros x phi M val.
  split.
  - intros Hnot.
    destruct (LEM (exists d : D M, ~ eval_form M (cng val x d) phi)) as [Hex | Hnex].
    + exact Hex.
    + exfalso. apply Hnot.
      intro d.
      destruct (LEM (eval_form M (cng val x d) phi)) as [Hphi | Hnotphi].
      * exact Hphi.
      * exfalso. apply Hnex. exists d. exact Hnotphi.
  - intros [d Hnotphi] Hall.
    apply Hnotphi. apply Hall.
Qed.
End ClassicalDuality.

(** SECTION 4: QUANTIFIER SHIFTING LAWS **)

Theorem shift_forall_conj_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FConj (FForall x phi) psi) (FForall x (FConj phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hall Hpsi] d.
    split.
    + apply Hall.
    + apply (Hnf M val d). exact Hpsi.
  - intros Hall.
    split.
    + intro d. apply (Hall d).
    + specialize (Hall (d0 M)).
      destruct Hall as [_ Hpsi_d].
      apply (Hnf M val (d0 M)). exact Hpsi_d.
Qed.

Theorem shift_forall_conj_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FConj psi (FForall x phi)) (FForall x (FConj psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hpsi Hall] d.
    split.
    + apply (Hnf M val d). exact Hpsi.
    + apply Hall.
  - intros Hall.
    split.
    + specialize (Hall (d0 M)).
      destruct Hall as [Hpsi_d _].
      apply (Hnf M val (d0 M)). exact Hpsi_d.
    + intro d. apply (Hall d).
Qed.

Theorem shift_exists_conj_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FConj (FExists x phi) psi) (FExists x (FConj phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [[d Hphi] Hpsi].
    exists d. split.
    + exact Hphi.
    + apply (Hnf M val d). exact Hpsi.
  - intros [d [Hphi Hpsi_d]].
    split.
    + exists d. exact Hphi.
    + apply (Hnf M val d). exact Hpsi_d.
Qed.

Theorem shift_exists_conj_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FConj psi (FExists x phi)) (FExists x (FConj psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hpsi [d Hphi]].
    exists d. split.
    + apply (Hnf M val d). exact Hpsi.
    + exact Hphi.
  - intros [d [Hpsi_d Hphi]].
    split.
    + apply (Hnf M val d). exact Hpsi_d.
    + exists d. exact Hphi.
Qed.

Theorem shift_exists_disj_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FDisj (FExists x phi) psi) (FExists x (FDisj phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [[d Hphi] | Hpsi].
    + exists d. left. exact Hphi.
    + exists (d0 M). right. apply (Hnf M val (d0 M)). exact Hpsi.
  - intros [d [Hphi | Hpsi_d]].
    + left. exists d. exact Hphi.
    + right. apply (Hnf M val d). exact Hpsi_d.
Qed.

Theorem shift_exists_disj_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FDisj psi (FExists x phi)) (FExists x (FDisj psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hpsi | [d Hphi]].
    + exists (d0 M). left. apply (Hnf M val (d0 M)). exact Hpsi.
    + exists d. right. exact Hphi.
  - intros [d [Hpsi_d | Hphi]].
    + left. apply (Hnf M val d). exact Hpsi_d.
    + right. exists d. exact Hphi.
Qed.

Theorem shift_forall_impl_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FImpl psi (FForall x phi)) (FForall x (FImpl psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros Himpl d Hpsi_d.
    apply Himpl.
    + apply (Hnf M val d). exact Hpsi_d.
  - intros Hall Hpsi d.
    apply (Hall d).
    apply (Hnf M val d). exact Hpsi.
Qed.

Theorem shift_exists_impl_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FImpl (FExists x phi) psi) (FForall x (FImpl phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros Himpl d Hphi.
    apply (Hnf M val d).
    apply Himpl.
    exists d. exact Hphi.
  - intros Hall [d Hphi].
    apply (Hnf M val d).
    apply (Hall d).
    exact Hphi.
Qed.

Section ClassicalShifting.
Variable LEM : forall P : Prop, P \/ ~ P.

Theorem shift_forall_disj_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FDisj (FForall x phi) psi) (FForall x (FDisj phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hall | Hpsi] d.
    + left. apply Hall.
    + right. apply (Hnf M val d). exact Hpsi.
  - intros Hall.
    destruct (LEM (eval_form M val psi)) as [Hpsi | Hnotpsi].
    + right. exact Hpsi.
    + left. intro d.
      destruct (Hall d) as [Hphi | Hpsi_d].
      * exact Hphi.
      * exfalso. apply Hnotpsi.
        apply (Hnf M val d). exact Hpsi_d.
Qed.

Theorem shift_forall_disj_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FDisj psi (FForall x phi)) (FForall x (FDisj psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros [Hpsi | Hall] d.
    + left. apply (Hnf M val d). exact Hpsi.
    + right. apply Hall.
  - intros Hall.
    destruct (LEM (eval_form M val psi)) as [Hpsi | Hnotpsi].
    + left. exact Hpsi.
    + right. intro d.
      destruct (Hall d) as [Hpsi_d | Hphi].
      * exfalso. apply Hnotpsi.
        apply (Hnf M val d). exact Hpsi_d.
      * exact Hphi.
Qed.

Theorem shift_exists_impl_r : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FImpl psi (FExists x phi)) (FExists x (FImpl psi phi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros Himpl.
    destruct (LEM (eval_form M val psi)) as [Hpsi | Hnotpsi].
    + destruct (Himpl Hpsi) as [d Hphi].
      exists d. intro Hpsi_d. exact Hphi.
    + exists (d0 M). intro Hpsi_d.
      exfalso. apply Hnotpsi.
      apply (Hnf M val (d0 M)). exact Hpsi_d.
  - intros [d Himpl_d] Hpsi.
    exists d. apply Himpl_d.
    apply (Hnf M val d). exact Hpsi.
Qed.

Theorem shift_forall_impl_l : forall x phi psi,
  not_free_in x psi ->
  sem_equiv (FImpl (FForall x phi) psi) (FExists x (FImpl phi psi)).
Proof.
  intros x phi psi Hnf M val.
  split.
  - intros Himpl.
    destruct (LEM (eval_form M val (FForall x phi))) as [Hall | Hnall].
    + exists (d0 M). intro Hphi_d.
      apply (Hnf M val (d0 M)). apply Himpl. exact Hall.
    + destruct (LEM (exists d : D M, ~ eval_form M (cng val x d) phi)) as [[d Hnotphi] | Hnex].
      * exists d. intro Hphi. exfalso. apply Hnotphi. exact Hphi.
      * exfalso. apply Hnall. intro d.
        destruct (LEM (eval_form M (cng val x d) phi)) as [Hphi | Hnotphi].
        -- exact Hphi.
        -- exfalso. apply Hnex. exists d. exact Hnotphi.
  - intros [d Himpl_d] Hall.
    apply (Hnf M val d).
    apply Himpl_d.
    apply (Hall d).
Qed.

End ClassicalShifting.

(** SECTION 5: PRENEX NORMAL FORM **)

Inductive is_quantifier_free : formula -> Prop :=
| qf_atom : forall p ts, is_quantifier_free (FAtom p ts)
| qf_bot : is_quantifier_free FBot
| qf_conj : forall phi psi, is_quantifier_free phi -> is_quantifier_free psi -> is_quantifier_free (FConj phi psi)
| qf_disj : forall phi psi, is_quantifier_free phi -> is_quantifier_free psi -> is_quantifier_free (FDisj phi psi)
| qf_impl : forall phi psi, is_quantifier_free phi -> is_quantifier_free psi -> is_quantifier_free (FImpl phi psi).

Inductive is_prenex_form : formula -> Prop :=
| prenex_qf : forall phi, is_quantifier_free phi -> is_prenex_form phi
| prenex_forall : forall x phi, is_prenex_form phi -> is_prenex_form (FForall x phi)
| prenex_exists : forall x phi, is_prenex_form phi -> is_prenex_form (FExists x phi).

Inductive quantifier : Type := QForall | QExists.
Definition prefix := list (quantifier * nat).

Fixpoint apply_prefix (pfx : prefix) (matrix : formula) : formula :=
  match pfx with
  | nil => matrix
  | (QForall, x) :: rest => FForall x (apply_prefix rest matrix)
  | (QExists, x) :: rest => FExists x (apply_prefix rest matrix)
  end.

Lemma apply_prefix_prenex : forall pfx matrix,
  is_quantifier_free matrix ->
  is_prenex_form (apply_prefix pfx matrix).
Proof.
  induction pfx as [ | [q x] rest IH ]; intros matrix Hqf; simpl.
  - apply prenex_qf. exact Hqf.
  - destruct q.
    + apply prenex_forall. apply IH. exact Hqf.
    + apply prenex_exists. apply IH. exact Hqf.
Qed.

Fixpoint quantifier_prefix (phi : formula) : prefix :=
  match phi with
  | FForall x psi => (QForall, x) :: quantifier_prefix psi
  | FExists x psi => (QExists, x) :: quantifier_prefix psi
  | _ => nil
  end.

Fixpoint matrix (phi : formula) : formula :=
  match phi with
  | FForall _ psi => matrix psi
  | FExists _ psi => matrix psi
  | other => other
  end.

Lemma qf_prefix_nil : forall phi,
  is_quantifier_free phi -> quantifier_prefix phi = nil /\ matrix phi = phi.
Proof.
  intros phi Hqf.
  induction Hqf; simpl; auto.
Qed.

Theorem matrix_prefix_decomp : forall phi,
  is_prenex_form phi ->
  phi = apply_prefix (quantifier_prefix phi) (matrix phi) /\ is_quantifier_free (matrix phi).
Proof.
  intros phi Hprenex.
  induction Hprenex.
  - destruct (qf_prefix_nil phi H) as [Hp Hm].
    simpl. rewrite Hp, Hm. simpl.
    split; [ reflexivity | exact H ].
  - destruct IHHprenex as [Heq Hqf].
    simpl.
    split.
    + rewrite <- Heq. reflexivity.
    + exact Hqf.
  - destruct IHHprenex as [Heq Hqf].
    simpl.
    split.
    + rewrite <- Heq. reflexivity.
    + exact Hqf.
Qed.

Theorem prenex_normal_form_qf : forall phi,
  is_quantifier_free phi -> is_prenex_form phi.
Proof.
  intros phi Hqf.
  apply prenex_qf. exact Hqf.
Qed.

Theorem prenex_normal_form_apply_prefix : forall pfx phi,
  is_quantifier_free phi ->
  is_prenex_form (apply_prefix pfx phi).
Proof.
  intros pfx phi Hqf.
  apply apply_prefix_prenex. exact Hqf.
Qed.

Theorem prenex_forall_step : forall x phi,
  is_prenex_form phi ->
  is_prenex_form (FForall x phi).
Proof.
  intros x phi Hpr.
  apply prenex_forall. exact Hpr.
Qed.

Theorem prenex_exists_step : forall x phi,
  is_prenex_form phi ->
  is_prenex_form (FExists x phi).
Proof.
  intros x phi Hpr.
  apply prenex_exists. exact Hpr.
Qed.

Theorem prenex_equiv_for_prenex : forall phi,
  is_prenex_form phi ->
  exists psi, is_prenex_form psi /\ sem_equiv phi psi.
Proof.
  intros phi Hpr.
  exists phi.
  split; [ exact Hpr | intros M val; reflexivity ].
Qed.

Theorem prenex_equiv_for_prefix : forall pfx phi,
  is_quantifier_free phi ->
  exists psi, is_prenex_form psi /\ sem_equiv (apply_prefix pfx phi) psi.
Proof.
  intros pfx phi Hqf.
  exists (apply_prefix pfx phi).
  split.
  - apply apply_prefix_prenex. exact Hqf.
  - intros M val. reflexivity.
Qed.

Theorem prenex_normal_form_exists_qf : forall phi,
  is_quantifier_free phi ->
  exists psi, is_prenex_form psi /\ sem_equiv phi psi.
Proof.
  intros phi Hqf.
  exists phi.
  split.
  - apply prenex_qf. exact Hqf.
  - intros M val. reflexivity.
Qed.

(** SECTION 6: HILBERT-STYLE FIRST-ORDER DERIVATION AND DEDUCTION THEOREM **)

Inductive Prf : list formula -> formula -> Prop :=
| H_hyp : forall ctx A, In A ctx -> Prf ctx A
| H_Ax_K : forall ctx A B, Prf ctx (FImpl A (FImpl B A))
| H_Ax_S : forall ctx A B C, Prf ctx (FImpl (FImpl A (FImpl B C)) (FImpl (FImpl A B) (FImpl A C)))
| H_Ax_Conj1 : forall ctx A B, Prf ctx (FImpl (FConj A B) A)
| H_Ax_Conj2 : forall ctx A B, Prf ctx (FImpl (FConj A B) B)
| H_Ax_ConjIntro : forall ctx A B, Prf ctx (FImpl A (FImpl B (FConj A B)))
| H_Ax_Disj1 : forall ctx A B, Prf ctx (FImpl A (FDisj A B))
| H_Ax_Disj2 : forall ctx A B, Prf ctx (FImpl B (FDisj A B))
| H_Ax_DisjElim : forall ctx A B C, Prf ctx (FImpl (FImpl A C) (FImpl (FImpl B C) (FImpl (FDisj A B) C)))
| H_Ax_BotElim : forall ctx A, Prf ctx (FImpl FBot A)
| H_MP : forall ctx A B, Prf ctx A -> Prf ctx (FImpl A B) -> Prf ctx B
| H_GEN : forall ctx x A, (forall B, In B ctx -> free_in x B = false) -> Prf ctx A -> Prf ctx (FForall x A)
| H_Ax_AllInst : forall ctx x t A, Prf ctx (FImpl (FForall x A) (subst_form t x A))
| H_Ax_ExIntro : forall ctx x t A, Prf ctx (FImpl (subst_form t x A) (FExists x A))
| H_Ax_AllShift : forall ctx x A B, free_in x B = false -> Prf ctx (FImpl (FForall x (FImpl B A)) (FImpl B (FForall x A)))
| H_Ax_ExShift : forall ctx x A B, free_in x B = false -> Prf ctx (FImpl (FForall x (FImpl A B)) (FImpl (FExists x A) B)).

Lemma Prf_AtoA : forall ctx A, Prf ctx (FImpl A A).
Proof.
  intros ctx A.
  eapply H_MP with (A := FImpl A (FImpl A A)).
  - apply H_Ax_K.
  - eapply H_MP with (A := FImpl A (FImpl (FImpl A A) A)).
    + apply H_Ax_K.
    + apply H_Ax_S.
Qed.

Lemma Prf_weaken : forall ctx A B,
  Prf ctx B ->
  (forall x, (forall C, In C ctx -> free_in x C = false) -> free_in x A = false) ->
  Prf (A :: ctx) B.
Proof.
  intros ctx A B Hprf.
  revert A.
  induction Hprf; intros A0 Hcond.
  - apply H_hyp. right. exact H.
  - apply H_Ax_K.
  - apply H_Ax_S.
  - apply H_Ax_Conj1.
  - apply H_Ax_Conj2.
  - apply H_Ax_ConjIntro.
  - apply H_Ax_Disj1.
  - apply H_Ax_Disj2.
  - apply H_Ax_DisjElim.
  - apply H_Ax_BotElim.
  - eapply H_MP.
    + apply IHHprf1. exact Hcond.
    + apply IHHprf2. exact Hcond.
  - apply H_GEN.
    + intros C [Heq | Hin].
      * subst C. apply Hcond. exact H.
      * apply H. exact Hin.
    + apply IHHprf. exact Hcond.
  - apply H_Ax_AllInst.
  - apply H_Ax_ExIntro.
  - apply H_Ax_AllShift. exact H.
  - apply H_Ax_ExShift. exact H.
Qed.

Theorem Prf_deduction_converse : forall ctx A B,
  Prf ctx (FImpl A B) ->
  (forall x, (forall C, In C ctx -> free_in x C = false) -> free_in x A = false) ->
  Prf (A :: ctx) B.
Proof.
  intros ctx A B Himpl Hcond.
  eapply H_MP with (A := A).
  - apply H_hyp. left. reflexivity.
  - apply Prf_weaken; assumption.
Qed.

Theorem Prf_deduction_direct : forall ctx A B,
  Prf (A :: ctx) B ->
  Prf ctx (FImpl A B).
Proof.
  intros ctx A B Hprf.
  remember (A :: ctx) as Gamma eqn:E.
  revert ctx E.
  induction Hprf; intros ctx0 E.
  - subst ctx. simpl in H.
    destruct H as [Heq | Hin].
    + subst A0. apply Prf_AtoA.
    + eapply H_MP with (A := A0).
      * apply H_hyp. exact Hin.
      * apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl A0 (FImpl B A0)).
    + apply H_Ax_K.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FImpl A0 (FImpl B C)) (FImpl (FImpl A0 B) (FImpl A0 C))).
    + apply H_Ax_S.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FConj A0 B) A0).
    + apply H_Ax_Conj1.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FConj A0 B) B).
    + apply H_Ax_Conj2.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl A0 (FImpl B (FConj A0 B))).
    + apply H_Ax_ConjIntro.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl A0 (FDisj A0 B)).
    + apply H_Ax_Disj1.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl B (FDisj A0 B)).
    + apply H_Ax_Disj2.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FImpl A0 C) (FImpl (FImpl B C) (FImpl (FDisj A0 B) C))).
    + apply H_Ax_DisjElim.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl FBot A0).
    + apply H_Ax_BotElim.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl A A0).
    + apply (IHHprf1 ctx0 eq_refl).
    + eapply H_MP with (A := FImpl A (FImpl A0 B)).
      * apply (IHHprf2 ctx0 eq_refl).
      * apply H_Ax_S.
  - subst ctx.
    assert (HnA : free_in x A = false).
    { apply H. left. reflexivity. }
    assert (Hnctx : forall B, In B ctx0 -> free_in x B = false).
    { intros C HC. apply H. right. exact HC. }
    eapply H_MP with (A := FForall x (FImpl A A0)).
    + apply H_GEN.
      * exact Hnctx.
      * apply (IHHprf ctx0 eq_refl).
    + apply H_Ax_AllShift. exact HnA.
  - subst ctx.
    eapply H_MP with (A := FImpl (FForall x A0) (subst_form t x A0)).
    + apply H_Ax_AllInst.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (subst_form t x A0) (FExists x A0)).
    + apply H_Ax_ExIntro.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FForall x (FImpl B A0)) (FImpl B (FForall x A0))).
    + apply H_Ax_AllShift. exact H.
    + apply H_Ax_K.
  - subst ctx.
    eapply H_MP with (A := FImpl (FForall x (FImpl A0 B)) (FImpl (FExists x A0) B)).
    + apply H_Ax_ExShift. exact H.
    + apply H_Ax_K.
Qed.

Theorem Prf_deduction_iff : forall ctx A B,
  (forall x, (forall C, In C ctx -> free_in x C = false) -> free_in x A = false) ->
  (Prf (A :: ctx) B <-> Prf ctx (FImpl A B)).
Proof.
  intros ctx A B Hcond.
  split.
  - apply Prf_deduction_direct.
  - intro H. apply Prf_deduction_converse; assumption.
Qed.

(** SECTION 7: SKOLEM NORMAL FORM AND EQUISATISFIABILITY **)

Inductive is_skolem_form : formula -> Prop :=
| skolem_qf : forall phi, is_quantifier_free phi -> is_skolem_form phi
| skolem_forall : forall x phi, is_skolem_form phi -> is_skolem_form (FForall x phi).

Theorem skolem_is_prenex : forall phi,
  is_skolem_form phi -> is_prenex_form phi.
Proof.
  induction 1.
  - apply prenex_qf. exact H.
  - apply prenex_forall. exact IHis_skolem_form.
Qed.

Section SkolemEquisatisfiability.

Variable D_dom : Type.
Variable R_rel : D_dom -> D_dom -> Prop.

Theorem skolem_functional_equisatisfiable :
  (exists f : D_dom -> D_dom, forall x : D_dom, R_rel x (f x)) ->
  (forall x : D_dom, exists y : D_dom, R_rel x y).
Proof.
  intros [f Hf] x.
  exists (f x).
  apply Hf.
Qed.

Theorem skolem_constant_equisatisfiable :
  (exists y : D_dom, forall x : D_dom, R_rel x y) ->
  (forall x : D_dom, exists y : D_dom, R_rel x y).
Proof.
  intros [y Hy] x.
  exists y.
  apply Hy.
Qed.

Theorem skolem_choice_equisatisfiable :
  (forall (R0 : D_dom -> D_dom -> Prop),
     (forall x, exists y, R0 x y) -> exists f : D_dom -> D_dom, forall x, R0 x (f x)) ->
  ((forall x : D_dom, exists y : D_dom, R_rel x y) <->
   (exists f : D_dom -> D_dom, forall x : D_dom, R_rel x (f x))).
Proof.
  intro Hchoice.
  split.
  - apply Hchoice.
  - apply skolem_functional_equisatisfiable.
Qed.

End SkolemEquisatisfiability.
