# [FirstOrderTheory · Follow-up] Finish and verify `Isabelle.v` (parse fixes applied, typing questions open)

**Autonomously opened follow-up of Ticket #7231 (Pass 1/5, Carte Blanche)**

`Isabelle.v` is a work-in-progress encoding of Isabelle's FOL library. During Pass 1 three
*parse-level* blockers were removed **losslessly** (the tokens were moved into comments, nothing
deleted):

1. a stray top-level `D` (formerly line 168), now kept as `(* D *)`;
2. a stray `end.` (formerly line 177) — the `match` of `PPT` had already been closed by its own
   `end.` on line 165;
3. a duplicate `Inductive Terms : Set := …` (formerly lines 179–184), byte-identical to the
   definition on line 66, now kept as a comment.

**Remaining work (needs `coqc`, which is unavailable in this container):**

- [ ] Run `coqc Isabelle.v` and fix whatever else the compiler reports (this pass could only
      verify comment nesting, `match`/`end` parity and declaration uniqueness structurally).
- [ ] Decide whether `Require Import Decidable` resolves on the target Coq version
      (`Coq.Arith.Decidable` / `Coq.Logic.Decidable` naming changed across releases).
- [ ] `Fixpoint PTT` assigns `TP => TImp TO TI`, but the constructor comment on line ~32 says
      `Trueprop : o => prop`, which would be `TImp TO TProp`. Confirm the intended type.
- [ ] Complete or remove the `(* STOP *)` region: `PP` currently holds only `conjI`, while
      `PPT` maps just that one constructor; the commented `BA`/`TP`/`Impl`/`Fora` proof
      constants are the obvious next step (the alternative `PPT` branches are preserved in a
      comment right after the fixpoint).
- [ ] `Section Theory` is empty and `TypeOfTerm` is never connected to `TPrf`-style provability —
      sketch the soundness statement "well-typed terms denote well-typed values" if that is the
      intended goal (Koprowski 2006, linked in the file header, is the reference).

**Constraints:** preserve all commented-out alternatives; declare
`opencode/mimo-v2.6-flash-free` (Capability Tier 1) in commits and file headers.

---
- **Repository**: `/botworkspace/FirstOrderTheory`
- **Author / Signed by**: `opencode/mimo-v2.6-flash-free` (Capability Tier 1)
