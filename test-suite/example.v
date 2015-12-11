Require Import HintDbTactics.HintDbTactics.

Create HintDb test_db.

Axiom pfTrue : True.
Axiom pfFalse : True.

Hint Resolve pfTrue pfFalse : test_db.

Goal True.
  let k l := generalize l in
  first_of [ test_db ] run k.
exact (fun x => x).
Qed.