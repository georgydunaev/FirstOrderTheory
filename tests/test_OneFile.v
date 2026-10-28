Require Import OneFile.

Test "Terms_ind" : forall (T : Terms -> Prop) (H_FVC : forall sv, T (FVC sv)) (H_FSC : forall (f:FSV) (v:Vector.t Terms (fsv f)), (forall i, T (Vector.nth v i)) -> T (FSC f v)) (t:Terms), T t.
  intros T H_FVC H_FSC t.
  apply Terms_ind.
  exact (H_FVC, H_FSC).
Qed.