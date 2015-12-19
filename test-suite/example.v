Require Import HintDbTactics.HintDbTactics.

Create HintDb test_db.

Axiom pfTrue : True.
Axiom pfFalse : True.

Hint Resolve pfTrue pfFalse : test_db.

Goal True.
  let k l := pose l in
  foreach [ rev(db:test_db) ] k.
  exact I.
Defined.

Goal True.
  let k l := exact l in
  first_of [ db:test_db db:core ] k.
Qed.