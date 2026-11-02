(* logical_tautology.v -- Coq proof of the first-order argument form:
   ((forall x : D, P x /\ Q x -> R x) /\ (exists x : D, P x /\ Q x))
     -> (exists x : D, R x)
*)

Section LogicalTautology.

Variable D : Type.
Variables P Q R : D -> Prop.

Theorem existential_modus_ponens :
  (forall x : D, P x /\ Q x -> R x) ->
  (exists x : D, P x /\ Q x) ->
  (exists x : D, R x).
Proof.
  intros H_univ H_ex.
  destruct H_ex as [x0 H_pq].
  exists x0.
  apply H_univ.
  exact H_pq.
Qed.

End LogicalTautology.
