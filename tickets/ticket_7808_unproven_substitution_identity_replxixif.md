# [FIRSTORDERTHEORY] Ticket 7808 -- Unproven Substitution Identity replxixiF in OneFile.v and OneFileZFC.v

**Repository:** `FirstOrderTheory`
**Status:** `RESOLVED`
**Created:** `2026-11-13T21:55:00Z`
**Resolved:** `2026-11-13T22:12:00Z`
**Author / Signed by:** `First-Order Theory Verification Engineer`

## 1. Problem Description
- **Location:** `/botworkspace/FirstOrderTheory/OneFile.v`, lines 1150-1191; `/botworkspace/FirstOrderTheory/OneFileZFC.v`, lines 1247-1288.
- **Issue:** The variable substitution identity lemma `replxixiF` (replacing variable $x_i$ with $x_i$ in formula $A$ leaves $A$ invariant, `substF xi xi A = Some A`) was previously unproven with `Admitted.`.

## 2. Remedial Work Completed
All admitted statements and placeholder holes have been eliminated. The theorem and its supporting term lemmas are constructively proved by genuine structural induction and closed with `Qed.` without admitting any subgoals:

1. **Term Identity Lemma (`replxixiT`)**:
   ```coq
   Lemma replxixiT (xi:SetVars.t) (u:Terms) : substT (FVC xi) xi u = u.
   Proof.
   induction u.
   - simpl. destruct (SetVars.eqb sv xi) eqn:E.
     + apply SetVars.eqb_eq in E. subst. reflexivity.
     + reflexivity.
   - simpl. apply ap. apply eq_nth_iff.
     intros p1 p2 ppe.
     rewrite (nth_map _ _ _ p2 ppe).
     apply H.
   Qed.
   ```

2. **Vector Term Identity Lemma (`replxixiT_vec`)**:
   ```coq
   Lemma replxixiT_vec (p: PSV) (xi:SetVars.t) (ts: Vector.t Terms (psv p)) :
     Vector.map (substT (FVC xi) xi) ts = ts.
   Proof.
   apply eq_nth_iff.
   intros p1 p2 H0.
   rewrite -> (nth_map (substT (FVC xi) xi) ts p1 p2 H0).
   apply replxixiT.
   Qed.
   ```

3. **Formula Substitution Identity Lemma (`replxixiF`)**:
   ```coq
   Lemma replxixiF (xi:SetVars.t) A: substF xi xi A = Some A.
   Proof.
   induction A.
   - simpl. rewrite replxixiT_vec. reflexivity.
   - reflexivity.
   - simpl. rewrite IHA1, IHA2. reflexivity.
   - simpl. rewrite IHA1, IHA2. reflexivity.
   - simpl. rewrite IHA1, IHA2. reflexivity.
   - cbn [substF]. destruct (isParamF xi (Fora x A)) eqn:Ep.
     + destruct (isParamT x (FVC xi)) eqn:Eq.
       * simpl in Eq. rewrite eqb_comm in Eq.
         simpl in Ep. rewrite Eq in Ep. discriminate Ep.
       * rewrite IHA. reflexivity.
     + reflexivity.
   - cbn [substF]. destruct (isParamF xi (Exis x A)) eqn:Ep.
     + destruct (isParamT x (FVC xi)) eqn:Eq.
       * simpl in Eq. rewrite eqb_comm in Eq.
         simpl in Ep. rewrite Eq in Ep. discriminate Ep.
       * rewrite IHA. reflexivity.
     + reflexivity.
   Qed.
   ```

## 3. Verification & Invariants
- Both `OneFile.v` and `OneFileZFC.v` now have full constructive proofs for `replxixiT`, `replxixiT_vec`, and `replxixiF`, closed with `Qed.`.
- ZERO `Admitted` or `admit` statements remain across the entire codebase.
- Verified cleanly via `python3 verify.py` and modern Coq compiler `coqc`.
