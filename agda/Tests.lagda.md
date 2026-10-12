# Illustrative Tests

The tests below illustrate *automatic* proof by the Agda type-checker that
the denotations of some terms compute the expected values.
The type-correctness of the `refl` definitions of the declared equivalences
confirms that they hold.

Apart from confirming that a denotational semantics defines denotations
which compute the expected values at least for some terms,
the tests also depend on the imported rewrite rules for [postulated properties].
The success of those tests indirectly checks that the rewrite rules preserve denotations.
(A more systematic approach would be to develop a suite of unit tests for consequences of postulated properties.)
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests where
  import Tests.LC
  import Tests.PCF
```

We leave development of significant tests for the `Scm` language to future work.
This is partly because the published denotational definition of *Scm* [(Mosses2025CDS)]
leaves various domains and operations completely unspecified, and our Agda embedding merely postulates them,
without specifying their properties.
Reduction of embedded denotations involving such operations by the Agda type-checker to (weak) head form
would not (in general) lead to particular elements of domains.

As a workaround, we could replace the embedded declarations of the postulated domains and operations
by definitions; e.g., the postulated type `Loc` of locations could be defined by `Loc = Nat`,
and the postulated operation `new` could then be defined to give the first location
mapped to `unallocated` by the current store.
But that would undermine the correspondence between the published denotational semantics
and its Agda embedding.

[Postulated Properties]: ../Properties/index.md#postulated-properties
[(Mosses2025CDS)]: https://doi.org/10.1145/3759537.3762694
