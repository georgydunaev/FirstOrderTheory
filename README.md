# FirstOrderTheory

**A Coq development of intuitionistic first-order logic in Hilbert style — with a machine-checked
relative *soundness* theorem — plus a membership-only fragment that extracts to OCaml, and three
experimental encodings of Isabelle's FOL/HOL libraries.**

> **Provenance / authorship of this document**
>
> - **Sources**: all Coq (`.v`) and OCaml (`.ml`) files are the work of the upstream repository
>   author, *Georgy Dunaev* \<georgedunaev@gmail.com\> (see the header comment of `OneFile.v` /
>   `OneFileZFC.v`). Nothing in the sources was deleted or rewritten by this pass.
> - **This README**, the structural test suite (`tests/`), the `make test` target, the
>   *parse-level* fixes in `Isabelle.v`, and the follow-up tickets `tickets/ticket_724*.md` were
>   produced for **Ticket #7231 — Pass 1/5 (Carte Blanche Exploration & Architecture README)** by
>   **`opencode/mimo-v2.6-flash-free`** (**Capability Tier 1**) on 2026-10-27.
> - **Preservation policy**: alternative proofs, abandoned attempts and work-in-progress blocks
>   remain in the sources as comments (§7). This repository follows a "never discard an approach"
>   rule.

---

## 1. Contents at a glance

| File | Lines | What it is | State |
|---|---:|---|---|
| `OneFile.v` | 1208 | **Main development.** Parametric intuitionistic predicate calculus: syntax, capture-avoiding substitution, semantics, Hilbert-style calculus, and the `soundness` theorem inside module `ALL_mod`. | Mainline; one `Admitted` hole (`replxixiF`, §6) |
| `OneFileZFC.v` | 1303 | Membership-only (`∈`-only) variant of the same calculus, written to be **extracted to OCaml** (`Extraction "prog.ml" PREPR.`). The complete general development is preserved verbatim inside a trailing block comment. | Active head = lines 1–228; preserved comment = lines 235–1303 |
| `Isabelle.v` | 230 | Sketch of *Isabelle's FOL library*: the `Types`/`PT`/`PP` hierarchies, typed terms, a type-checking function `TypeOfTerm`, and the ∧-introduction rule encoded as a term (`conjI_type`). | Work in progress (`(* STOP *)` marker); parse blockers removed in this pass, compilation still unverified (§5, §6) |
| `IsabelleAlt.v` | 126 | A proof-relevant natural-deduction/Hilbert model of Isabelle's `o` / `prop` / `Prf` metalogic, with the deduction theorem and weakening rules. | WIP: `Deduction` is `Abort`ed; file ends with a body-less `Fixpoint q` |
| `OneFileIsabelle.v` | 114 | A typed derivation system `TPrf : TCtx -> Terms -> Types -> Type` (terms with λ-abstraction and application) intended as "higher-order logic needed for Isabelle/ZF". | WIP: `dosubst` and `PELam` carry `TODO` markers |
| `printer.ml` | 18 | OCaml stub meant to pretty-print extracted proofs (`printerFm`, `printerPrf`); currently returns placeholder strings and prints `Prog.thm2`. | Stub (§6, ticket #7242) |
| `Makefile` | 10 | `make go` — the OCaml pipeline (`ocamlc` over the extracted `prog.ml` + `printer.ml`); plus the new `make test` target added by this pass (the original `go` target is untouched). | `go` requires a generated `prog.ml` (§5) |
| `.gitignore` | 4 | Ignores `*.mli`, `*.pdf`, `*.cmi`, `*.cmo`, `a.out` (the generated `prog.ml` is deliberately *not* ignored — see ticket #7242). | Unchanged by this pass |
| `tickets/` | — | Delegated carte-blanche passes #7231–#7235 and the follow-up tickets opened by this pass (#7241–#7244). | Active |
| `tests/` | — | Structural regression tests that need **no Coq installation** (§5). | Added by this pass |

---

## 2. The logic that is formalised

The object of study is **intuitionistic first-order logic** (no law of excluded middle anywhere;
the propositional axioms below are the usual intuitionistic ones), presented in **Hilbert style
with a hypothesis context** and the usual side conditions on generalisation.

### 2.1 Bridge into Coq's `Prop`

Everything is written on top of a thin bridge layer (top of `OneFile.v` and `OneFileZFC.v`):

```coq
Notation Omega := Prop.            (* the type of object-level truth values *)
Definition OFalse := False.
Definition OAnd   := and.
Definition OOr    := or.
Definition OImp   := (fun x y : Omega => x -> y).
```

So the object logic's connectives are *interpreted by* Coq's own `False`, `/\`, `\/`, `->`.

### 2.2 Signatures, terms and formulas (`OneFile.v` §5–§7)

The whole development lives in a functor over an arbitrary finite-arity signature:

```coq
Module ALL_mod (SetVars FuncSymb PredSymb : UsualDecidableTypeFull).
```

Decidable equality on all three symbol types is what makes substitution and valuation update
computable (`SetVars.eqb`, …).

- **Terms** `Terms := FVC : SetVars.t -> Terms | FSC : FSV -> Vector.t Terms (fsv f) -> Terms`,
  i.e. variables plus function symbols applied to a vector of arguments whose length is dictated
  by the arity record `FSV := { fs : FuncSymb.t; fsv : nat }`. Because the inductive is *nested*
  inside `Vector.t`, the automatic elimination schemes are switched off and hand-written
  `Terms_ind` / `Terms_rect` / `Terms_rec` are provided.
- **Formulas** `Fo := Atom (p : PSV) (Vector.t Terms (psv p)) | Bot | Conj | Disj | Impl | Fora | Exis`
  with `PSV := { ps : PredSymb.t; psv : nat }` (arity-indexed atoms), derived `Neg A := Impl A Bot`
  and `Top := Neg Bot`, plus Unicode (`∧ ∨ → ∀ ∃ ¬ ⊥`) and ASCII (`-/\ -\/ --> -.`) notation scopes.
- **Occurrence test**: `isParamT` / `isParamF : SetVars.t -> _ -> bool` decide whether a variable
  occurs free (bound occurrences of the same variable stop the recursion — exactly the
  "is it a parameter?" question needed by the generalisation side condition).

### 2.3 Substitution (capture-aware, partial)

- `substT : Terms -> SetVars.t -> Terms -> Terms` — substitute a term for a free variable.
- `substF : Terms -> SetVars.t -> Fo -> option Fo` — **returns `None`** when the substitution
  would capture a bound variable (the `Fora`/`Exis` cases check `isParamF`/`isParamT` and give up
  rather than performing an incorrect capture). Partiality of `substF` is *by design*: the axiom
  schemes below are stated only for the `Some r` case, so no ill-formed substitution can ever be
  used in a proof.
- Support lemmas: `NPthenNCAST`, `NPthenNCAST_vec`, `NPthenNCASF` ("**n**ot a **p**arameter ⇒
  **n**ot **c**hanged **a**fter **s**ubstitution") built on the vector machinery of §3
  (`all_then_someV`, `ATS_B0`, `ATS_B2`, …).

### 2.4 Semantics

- Valuations are functions `val : SetVars.t -> X` for an arbitrary carrier `X : Type`;
  `cng val xi m` is the valuation updated at `xi` (`dbl_cng` : double update collapses).
- `teI : (SetVars.t -> X) -> Terms -> X` interprets terms (`FSC f v` is fed to the
  interpretation function `fsI : forall q : FSV, Vector.t X (fsv q) -> X`).
- `foI : (SetVars.t -> X) -> Fo -> Omega` interprets formulas; `Fora x f` becomes
  `forall m : X, foI (cng val x m) f`, `Exis x f` becomes `exists m : X, …`, and atoms are fed to
  `prI : forall q : PSV, Vector.t X (psv q) -> Omega`.

### 2.5 The calculus (`OneFile.v` §8)

*Axioms* — `PROCA` (intuitionistic propositional calculus, `Ha1`…`Ha10`):

| # | scheme |
|---|---|
| Ha1 | `A --> (B --> A)` |
| Ha2 | `(A --> (B --> C)) --> ((A --> B) --> (A --> C))` |
| Ha3/Ha4 | `A /\ B --> A`, `A /\ B --> B` |
| Ha5 | `A --> (B --> A /\ B)` |
| Ha6/Ha7 | `A --> A \/ B`, `B --> A \/ B` |
| Ha8 | `(A --> C) --> ((B --> C) --> (A \/ B --> C))` |
| Ha9 | `~A --> (A --> B)` |
| Ha10 | `(A --> B) --> ((A --> ~B) --> ~A)` |

*Predicate axioms* — `PRECA`:

- `PRO` lifts every `PROCA` axiom;
- `Ha12` (universal instantiation): `forall xi ph --> r` whenever `substF t xi ph = Some r`;
- `Ha13` (existential generalisation): `r --> exists xi ph` under the same premise;
- `Hb1` (a prenex "distribution" rule): `forall xi (ps --> ph) --> (ps --> forall xi ph)` when
  `isParamF xi ps = false`;
- `Hb2` (existential elimination): `forall xi (ph --> ps) --> (exists xi ph --> ps)` when
  `isParamF xi ps = false`.

*Proofs* — `PREPR (ctx : list Fo) : Fo -> Type`:

```coq
| hyp_E (A : Fo) : InL A ctx -> PREPR A                                  (* hypotheses *)
| Hax_E :> forall A, PRECA A -> PREPR A                                 (* axioms      *)
| MP_E (A B : Fo) : PREPR A -> PREPR (Impl A B) -> PREPR B              (* modus ponens *)
| GEN_E (A : Fo) (xi : SetVars.t) : NotParamC xi ctx ->                 (* generalisation, *)
    PREPR A -> PREPR (Fora xi A)                                        (* x not free in ctx *)
```

`InL` is list membership as a *Type* (`False | b = a | …`), and `NotParamC xi ctx` states that
`xi` is not a parameter of any formula in the context — the standard side condition.

### 2.6 Derived rules (all proved, not postulated)

`a1`, `a2`, `b1` (axiom instances), `AtoA : PREPR ctx (A --> A)`, `a1i` (deduction-step),
`B1` (**1st Bernays rule** admissible), `gen` (generalisation obtained from `B1`),
`Ded` — the **deduction theorem** `PREPR (A :: il) B -> PREPR il (A --> B)` (its `GEN` case is
where `Hb1` and the `NotParamC` side condition meet), and `swap_args`
`(A --> B --> C) --> (B --> A --> C)`.

> **Observation (not yet a lemma):** *ex falso quodlibet* is derivable even though it is not an
> axiom: `AtoA Bot : PREPR _ (Bot --> Bot)` proves `~Bot`, and `Ha9` instantiated at `A := Bot`
> gives `~Bot --> (Bot --> B)`; one MP yields `Bot --> B`. Recording this as a named lemma would
> make a good first example for the examples pass (ticket #7233).

### 2.7 The main theorem: soundness (`OneFile.v` §9)

Inside `Section cor` with an arbitrary carrier `X`, function interpretation `fsI` and predicate
interpretation `prI`:

```coq
Theorem soundness (f : Fo) (l : list Fo) (m : PREPR l f) :
  forall (val : SetVars.t -> X),
    (forall h : Fo, InL h l -> @foI X fsI prI val h) ->
    @foI X fsI prI val f.
```

> *Every derivable formula holds in every model under every valuation that satisfies the
> hypotheses.* The proof is by induction on the derivation and rests on two substitution lemmas
> cited from the author's reference book: `lem1` (p. 136, term substitution:
> `teI (substT t xi u) = teI (cng pi xi (teI pi t)) u`) and `lem2` (p. 137, formula substitution:
> `foI r <-> foI (cng pi xi (teI pi t)) fi` when `substF t xi fi = Some r`), with
> `UnivInst` / `ExisGene` as their corollaries for `Ha12` / `Ha13`.
>
> Note this is *relative* soundness: `X`, `fsI`, `prI` are arbitrary — no set-theoretic model is
> assumed. The theorem is closed with `Defined.` (transparent), so it can be used computationally.

Trailing material after the theorem: `replxixiF` (currently `Admitted`, §6),
`forall_swap`, and a `notation` section re-declaring `NTerms`/`NFo`.

---

## 3. `OneFileZFC.v` — the membership-only fragment

Head comment: *"here we prove theorem for \in only; then add and ="*.

The active part (lines 1–228) specialises the machinery of §2 to a **membership-only language**:

- `Terms` contains only variables (`FVC`); `fsunion` / `fspair` constructors exist but are kept
  commented out for a later extension.
- `AtomFm` contains only `IN x y`; the `EQ` atom is likewise commented out.
- Formulas `Fm` are the usual `Atom | Bot | Conj | Disj | Impl | Fora | Exis`.
- The carrier is `X := Se : nat -> X` and membership is currently interpreted by

  ```coq
  Definition In (x1 x2 : X) := match x1, x2 with Se n1, Se n2 => n1 < n2 end.
  ```

  i.e. **`∈` is modelled by `<` on natural numbers — a deliberate placeholder structure**, not a
  model of ZF (see the follow-up ticket #7243). Soundness for ZF-style axioms is therefore *not*
  claimed here; what this file does provide is the *syntactic* calculus plus extraction.
- The full intuitionistic calculus (`PROCA`, `PRECA`, `PREPR`) is re-stated, then:

  ```coq
  Extraction Language OCaml.
  Extraction "prog.ml" PREPR.      (* generates prog.ml, consumed by `make go` *)
  ```

- Everything after `(* HERE IS THE END OF THE CODE *)` (line 233) is the **complete general
  development preserved inside one block comment**, ending with `End ALL_mod.` — this is the
  "never delete an approach" guarantee in action and it is guarded by a regression test.

---

## 4. The Isabelle encodings

- **`Isabelle.v`** — *"Verification of Isabelle's FOL library"* (references the Koprowski 2006
  draft on type-checking in Isabelle). It builds the type language
  `Types := TVar | TImp | TProp | TO | TI` with decidable equality `eqTypes`, the primitive term
  constants `PT` (`LRA` = `==>`, `BA` = `!!`, `TP` = `Trueprop`, plus IFOL's `EFalse`, `Econj`,
  `Edisj`, `Eimp`) with their types `PTT`, and typed terms
  `Terms := EVar | ECon | ELam | EApp` together with a **partial type checker**
  `TypeOfTerm : Terms -> option Types` (returns `None` on ill-typed applications, using `eqTypes`).
  `conjI_type` encodes Isabelle's ∧-introduction rule *as a term*:
  `LRA (EVar 0) (LRA (EVar 1) (Econj (EVar 0) (EVar 1)))`, i.e. `⟦P; Q⟧ ⟹ P ∧ Q` in curried form.
  `PP` holds primitive proof constants; `PPT` gives them terms. The file stops at `(* STOP *)`
  (§6, ticket #7241).
- **`IsabelleAlt.v`** — a proof-relevant (`Prf : prop -> Type`) rendering of the metalogic:
  object formulas `o` (equality, `⊥`, `∧`, `→`), propositions `prop` (`ITrueprop`, `Iimpl`,
  `Iall`), axioms `A1`, `A2`, `MP`, `Irefl`, `Isubst`, `IimpI`, `Imp`, plus contexts `PrfCtx`.
  Proved: `assu : Prf (Iimpl P P)`, `dropL`, `dropR`, `TrueI : Prf (ITrue)`; `Deduction` is
  aborted; `bigunion` encodes the existential as an inductive type. The file ends mid-definition
  (§6, ticket #7244).
- **`OneFileIsabelle.v`** — declares `Types := TVar | TProp | TImp`, recursive type substitution
  `dosubst` with identity lemma `dosubst_id`, terms with λ (`EVar`, `ECon`, `EApp`, `ELam`), context
  extension `addtotctx`, and a typing judgment
  `TPrf : (nat -> Types) -> Terms -> Types -> Type` (hypothesis lookup `PEHyp`, constant typing
  `PEConType`, application `PEApp`, abstraction `PELam` using `addtotctx G x tau`), plus a separate
  `Proofs` datatype for *proof terms* (`PVar`, `PCon`, `PApp1/2`, `PLam1/2`).

---

## 5. Building and testing

```bash
# 1) Structural regression suite — needs only Python 3 (no Coq required):
python3 -m unittest discover -s tests -p 'test_*.py'
#    equivalently:  make test        (make(1) itself is NOT installed in this container)

# 2) The real Coq/OCaml pipeline — needs `coqc` and `ocamlc`:
coqc OneFileZFC.v  # type-checks the file and runs Extraction -> prog.ml
make go            # ocamlc -c/-o over prog.ml + printer.ml, then ./a.out
```

**Verification status of this pass (honest):** this container has **no `coqc`** and **no `make`**
(and `sudo` is blocked, so Coq cannot be installed), therefore the `.v` files could *not* be
machine-checked here. What *was* verified, by the test suite above (all 20 tests green):

1. nested `(* … *)` comments are balanced and never negatively nested in every `.v` file;
2. every `match` is closed by a matching `end` (parse-level parity) in every `.v` file;
3. no stray top-level tokens (e.g. a bare `D`) and no duplicate top-level `Inductive`/`Definition`
   names in any file;
4. `README.md` mentions every source file and declares the model provenance;
5. every open proof hole (`Admitted.`, `Abort.`, body-less `Fixpoint`) that exists in the sources
   is documented in §6 below — the tests fail if someone adds a hole without documenting it;
6. the preservation invariants of §3 (the trailing comment block of `OneFileZFC.v`) and the
   extraction directive still hold;
7. every file in `tickets/` has a title and a signed author line.

---

## 6. Known issues (all opened as follow-up tickets)

| # | Where | Issue | Ticket |
|---|---|---|---|
| 1 | `OneFile.v:1155` | `replxixiF : substF xi xi A = Some A` is **`Admitted`** — the only hole in the mainline. `forall_swap` is proved *on top of* it, so it currently rests on an axiom. (The lemma is provable by induction on `A`; see ticket.) | #7244 |
| 2 | `OneFile.v:1157` | `forall_swap` is stated as `PREPR nil (Fora y (Fora x A) --> Fora y (Fora x A))` — **both sides are identical**, so it does not swap anything; the RHS was almost certainly meant to be `Fora x (Fora y A)`. | #7244 |
| 3 | `Isabelle.v` | Three parse blockers (a stray top-level `D`, a stray `end.`, a duplicate `Inductive Terms`) were **commented out (text preserved) in this pass**; the file still has a `(* STOP *)` marker, a suspicious `TP => TImp TO TI` (the constructor's own comment says `Trueprop : o => prop`), and the unverified `Require Import Decidable`. Compilation must be re-checked once `coqc` is available. | #7241 |
| 4 | `IsabelleAlt.v:70` | `Theorem Deduction (P Q:prop) (H : Prf P -> Prf Q) : Prf (Iimpl P Q).` ends in **`Abort.`** — the deduction theorem is missing. | #7244 |
| 5 | `IsabelleAlt.v:126` | The file **ends with a body-less** `Fixpoint q (n:nat) :=` (incomplete definition ⇒ parse error at EOF). | #7244 |
| 6 | `OneFileIsabelle.v` | `dosubst` (`Fixpoint` + `dosubst_id`) and `PELam` (`addtotctx G x tau`) implemented while preserving the original `TODO` variants in comments; `Proofs` typing judgment remains future work. | #7244 |
| 7 | `OneFileZFC.v:41-44` | `∈` is interpreted as `<` on `nat`; no ZF axioms, no `EQ` atom, no pairing/union terms yet — soundness w.r.t. real set membership is future work. | #7243 |
| 8 | `Makefile` / `printer.ml` | `make go` needs a `prog.mli` that `Extraction` does not produce, and `printer.ml` prints the stub `Prog.thm2`, which does not exist in the extracted output. The OCaml pipeline therefore cannot run end-to-end yet. | #7242 |
| 9 | environment | `coqc` is unavailable in this container, so none of the Coq files can be machine-checked in CI here; a `coqc`-based job (e.g. `coqc OneFile.v && coqc OneFileZFC.v`) is the natural next verification step. | #7242 |

---

## 7. Repository conventions

- **Never delete an approach.** Old proofs, abandoned definitions and experiments stay in the
  file as `(* … *)` comments (e.g. the second `AtoA` proof style in `OneFile.v`, the entire
  general development at the end of `OneFileZFC.v`, the `OLD` blocks in the Isabelle files).
  Regression tests enforce the two biggest of these.
- **Transparent proofs.** Completed proofs end with `Defined.` rather than `Qed.` so that they
  stay usable for computation/extraction; only genuinely open statements use `Admitted`/`Abort`
  and must be listed in §6.
- **Provenance.** Every commit, ticket and new file header of this collaboration declares the
  model identity `opencode/mimo-v2.6-flash-free` and capability tier (1).
- **Tickets.** Delegated passes live in `tickets/ticket_72xx_zone_delegated.md`; autonomously
  opened follow-ups use `tickets/ticket_72xx_followup_*.md`.

---

## 8. Follow-up tickets opened by this pass

| Ticket | Title |
|---|---|
| `tickets/ticket_7241_followup_isabelle_v.md` | Finish/verify `Isabelle.v` once `coqc` is available (parse fixes applied here + typing questions) |
| `tickets/ticket_7242_followup_build_extraction_pipeline.md` | Make the Coq → OCaml extraction pipeline (`prog.ml`, `printer.ml`, `make go`) actually run, and add a `coqc` CI job |
| `tickets/ticket_7243_followup_zfc_membership_semantics.md` | Give the `OneFileZFC.v` membership fragment a real semantics (`EQ`, pairing/union, ZF-style axioms) instead of the `<`-on-`nat` placeholder |
| `tickets/ticket_7244_followup_proof_holes_and_statement_typos.md` | Close the open proof holes and fix statement typos (`replxixiF`, `forall_swap`, `Deduction`, `Fixpoint q`, `dosubst`, `PELam`) |
