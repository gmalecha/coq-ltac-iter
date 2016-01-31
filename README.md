coq-ltac-iter
=============

A Coq plugin that provides a tactic that iterates over various collections of terms. For example,

```
Create HintDb my_lemmas.

Hint Resolve lem1 lem2 : my_lemmas.

Ltac the_tactic :=
  let k lem := idtac lem in
  foreach [ db:my_lemmas ] run k.
(* OUTPUT:
lem1
lem2
*)
```

There are three versions of the iterator

- ```foreach [ .. ] k``` combines the invocations of ```k``` using ```;```
- ```first_of [ .. ] k``` combines the invocations of ```k``` in the same was a ```first```
- ```plus_of [ .. ] k``` combines the invocations of ```k``` using ```+```

And there are several types of collections:

- ```*|-``` iterates premises bottom-to-top by default
- ```rev c``` reverses the iteration of ```c```
- ```db:h``` iterates the hints inside the hint database ```h```

Install from OPAM
-----------------
Make sure you added the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-ltac-iter