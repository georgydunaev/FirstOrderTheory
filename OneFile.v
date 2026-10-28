Definition Terms_ind (T : Terms -> Prop)
                       (H_FVC : forall sv, T (FVC sv))
                       (H_FSC : forall (f:FSV) (v:Vector.t Terms (fsv f)),
                                (forall i, T (Vector.nth v i)) -> T (FSC f v))
                       (t:Terms) : T t.

Theorem Terms_ind : forall (T : Terms -> Prop) (H_FVC : forall sv, T (FVC sv)) (H_FSC : forall (f:FSV) (v:Vector.t Terms (fsv f)), (forall i, T (Vector.nth v i)) -> T (FSC f v)) (t:Terms), T t.
Proof.
  induction t.
  - apply H_FVC.
  - apply H_FSC.
Qed.

(* Additional proofs and lemmas can be added here as needed. *)
                       (H_FVC : forall sv, T (FVC sv))
                       (H_FSC : forall (f:FSV) (v:Vector.t Terms (fsv f)),
                                (forall i, T (Vector.nth v i)) -> T (FSC f v))
                       (t:Terms) : T t.