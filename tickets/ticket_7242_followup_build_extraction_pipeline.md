# [FirstOrderTheory · Follow-up] Make the Coq → OCaml extraction pipeline actually run (and add a `coqc` check)

**Autonomously opened follow-up of Ticket #7231 (Pass 1/5, Carte Blanche)**

Current pipeline (as designed by the upstream author):

```
coqc OneFileZFC.v     # runs `Extraction Language OCaml. Extraction "prog.ml" PREPR.`
make go               # ocamlc -i printer.ml; ocamlc -c prog.mli; ocamlc -o a.out prog.ml printer.ml; ./a.out
```

**Why it cannot run end-to-end today:**

- [ ] `coqc` is not installed in this container (`sudo` is blocked by the `no new privileges`
      flag, so `apt-get install coq` is impossible). Install/provide Coq (or a CI job with
      `coqc OneFile.v && coqc OneFileZFC.v && coqc Isabelle.v …`) — this is the single most
      valuable verification step for the whole repository.
- [ ] `Extraction "prog.ml"` produces only `prog.ml`, but the Makefile runs `ocamlc -c prog.mli`
      first — there is no `.mli` in the repo and none is generated. Either drop that step or
      extract with `Extraction Blacklist`/separate interface generation.
- [ ] `printer.ml` prints `Prog.thm2`, which does **not** exist in the extracted output (the
      extraction target is the inductive `PREPR`). Replace the stub with a real pretty-printer
      for the extracted proof constructors, or extract a concrete example proof named `thm2`.
- [ ] `printer.ml` itself is a placeholder (`printerFm x = "ii"`, `printerPrf _ = "asdfgh"`).
- [ ] Decide whether generated artefacts (`prog.ml`, `*.vo`, `*.glob`) belong in `.gitignore`
      (currently `*.mli *.pdf *.cmi *.cmo a.out` are ignored, `prog.ml` is not, and it is not
      committed either).
- [ ] Optionally wire `make test` (structural suite added in Pass 1) into the workspace-level CI
      so regressions in comment balance / documentation coverage are caught automatically.

**Constraints:** never delete the existing `go` target or `printer.ml` stub history; declare
`opencode/mimo-v2.6-flash-free` (Capability Tier 1) in commits and file headers.

---
- **Repository**: `/botworkspace/FirstOrderTheory`
- **Author / Signed by**: `opencode/mimo-v2.6-flash-free` (Capability Tier 1)
