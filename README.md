coq-ltac-iter
=============

A Coq plugin that provides a tactic that iterates over various collections of terms. For example,

```
Create HintDb my_lemmas.

Hint Resolve lem1 lem2 : my_lemmas.

Ltac the_tactic :=
  let k lem := idtac lem in
  foreach [ db:my_lemmas ] k.
(* OUTPUT:
lem1
lem2
*)
```

There are three versions of the iterator

- ```foreach [ .. ] k``` combines the invocations of ```k``` using ```;```
- ```first_of [ .. ] k``` combines the invocations of ```k``` in the same way a ```first```
- ```plus_of [ .. ] k``` combines the invocations of ```k``` using ```+```

And there are several types of collections:

- ```*|-``` iterates premises bottom-to-top by default
- ```rev c``` reverses the iteration of ```c```
- ```db:h``` iterates the hints inside the hint database ```h```

Bugs & Feature Requests
-----------------------
Please submit bugs and feature requests to the [github issue tracker](https://github.com/gmalecha/coq-ltac-iter/issues).

Pull requests are also welcome.

Install from OPAM
-----------------
Make sure you added the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-ltac-iter

Install Manually
----------------
If you need to install the package manually then you will need to install the [PluginUtils](https://github.com/gmalecha/coq-plugin-utils) package first. After that, you can run:

    make install

to install this ltac-iter.
