Require Import Isabelle.

Test "Test TypeOfTerm for EVar".
  let t := EVar 0 in
  let expected := Some (I 0) in
  let actual := TypeOfTerm t in
  assert (actual = expected).

Test "Test TypeOfTerm for ECon".
  let t := ECon LRA in
  let expected := Some (PTT LRA) in
  let actual := TypeOfTerm t in
  assert (actual = expected).

Test "Test TypeOfTerm for ELam".
  let t := ELam 0 TO (EVar 0) in
  let expected := Some (TImp TO (I 0)) in
  let actual := TypeOfTerm t in
  assert (actual = expected).

Test "Test TypeOfTerm for EApp".
  let t1 := ELam 0 TO (EVar 0) in
  let t2 := ECon TP in
  let t := EApp t1 t2 in
  let expected := Some TO in
  let actual := TypeOfTerm t in
  assert (actual = expected).
