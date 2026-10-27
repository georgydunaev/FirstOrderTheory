# [FirstOrderTheory · Follow-up] Close the open proof holes and fix suspicious statements

**Autonomously opened follow-up of Ticket #7231 (Pass 1/5, Carte Blanche)**

Inventory of every unfinished statement found during the Pass-1 exploration (all of them are
also listed in `README.md` §6, which the structural test suite keeps in sync).

### 1. `OneFile.v:1155` — `replxixiF` is `Admitted`

```coq
Fixpoint replxixiF (xi:SetVars.t) A: substF xi xi A = Some A.
Proof. Admitted.
```

- This is the **only hole in the mainline development**, and `forall_swap` (proved right after)
  uses it, so `forall_swap` currently rests on an axiom.
- It is provable by structural induction on `A`:
  - atomic / connective cases are immediate from `simpl` and the `Some`-injection lemmas
    (`SomeInj`);
  - `Fora x psi` / `Exis x psi`: if `isParamF xi (Fora x psi) = false` the substitution already
    returns `Some _` unchanged; otherwise `SetVars.eqb x xi = false` (otherwise the `isParamF`
    test would have returned `false`), so `isParamT x (FVC xi) = false` and the recursion
    applies the induction hypothesis.
- Action: replace `Admitted` with that induction (keep a comment pointing to this ticket),
  then re-check `forall_swap`.

### 2. `OneFile.v:1157` — `forall_swap` does not swap anything

```coq
Lemma forall_swap A x y :
 PREPR nil (Fora y (Fora x A) --> Fora y (Fora x A)).
```

Both sides are **identical** (the RHS was almost certainly copy-pasted), so the lemma states
`P --> P`. The existing proof is a round trip — instantiate `y` and `x` with identity
substitutions (`Ha12 … replxixiF`), then generalise back — which is why it typechecks. Options:

- [ ] state the real permutation `PREPR nil (Fora y (Fora x A) --> Fora x (Fora y A))`
      (quantifier permutation *is* derivable in this Hilbert system: instantiate the outer
      quantifier, generalise the other variable under the `NotParamC` side condition, re-generalise),
      and adjust the proof; **or**
- [ ] keep the trivial statement but rename/document it honestly.

### 3. `IsabelleAlt.v:70` — the deduction theorem is `Abort`ed

```coq
Theorem Deduction (P Q:prop) (H : Prf P -> Prf Q) : Prf (Iimpl P Q).
Proof. Abort.
```

- [ ] Complete it (standard `A1`/`A2`/`MP` argument — note `assu`, `dropL`, `dropR` are already
      proved below and can be used as lemmas), or document why it is impossible in the current
      axiom set (the context-free `Prf` may need `PrfCtx`, which exists but is unused).

### 4. `IsabelleAlt.v:126` — file ends with a body-less definition

The last line is `Fixpoint q (n:nat) :=` with no body, which is a parse error at EOF.

- [ ] Supply the intended body (the surrounding comments discuss `bigunion`/`z`/`s` over `nat`,
      so `q` was likely meant to be an example of a type-level function), **or** comment the line
      out with a note — do not simply delete it.

### 5. `OneFileIsabelle.v:26,61` — two `TODO`s in the typed derivation system

- `Definition dosubst (subst : nat -> Types) (T : Types) : Types := T. (* TODO *)` — implement
  type substitution (needed for `PEConType` to be meaningful).
- `PELam … (* TODO: FIX! *)` — λ-abstraction currently does not extend the typing context;
  `TCtx := nat -> Types` and the commented-out `addtotctx` show the intended design.

**Constraints:** never delete a proof attempt — replace it with the completed version and keep
the old text as a comment if it differs; declare `opencode/mimo-v2.6-flash-free`
(Capability Tier 1) in commits and file headers; re-run `make test` (it fails if a new
`Admitted`/`Abort` is added without documenting it in `README.md` §6).

---
- **Repository**: `/botworkspace/FirstOrderTheory`
- **Author / Signed by**: `opencode/mimo-v2.6-flash-free` (Capability Tier 1)
