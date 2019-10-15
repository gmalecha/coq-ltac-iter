Require Import LtacIter.LtacIter.

(** * Iterating Hint Databases **)
Create HintDb test_db.

Axiom pfTrue : True.
Axiom pfFalse : True.

Hint Resolve pfTrue pfFalse : test_db.

Goal True.
  let k l := (idtac l) in
  foreach [ rev db:test_db ] k.
  exact I.
Defined.

Goal True.
  let k l := pose l in
  foreach [ db:core ] k.
  exact I.
Qed.

(** * Iterating Premises **)

Goal False -> True -> 1 = 1 -> True.
  intros.
  let k l := (apply l) in
  first_of [ *|- ] k.
Defined.

Goal True -> False -> 1 = 1 -> False.
  intros.
  let k l := (apply l) in
  first_of [ *|- ] k.
Defined.

Goal False -> True -> 1 = 1 -> True.
  intros.
  let k l := pose l in
  foreach [ rev *|- ] k.
  exact I.
Defined.

Goal True.
  foreach [ db:does_not_exist ] ltac:(fun x => idtac x).
  exact I.
Defined.
