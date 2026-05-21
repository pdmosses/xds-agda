# Illustrative Tests

The tests below illustrate *automatic* proof of equivalence of term denotations
by the Agda type-checker:
the type-correctness of the `refl` definitions of the declared equivalences
confirms that they hold.
Such tests can check that the denotation of a function call is equivalent to
the denotation of a constant in the embedding of a denotational semantics.
They can even check that a specific renaming preserves the denotation of a term.

Apart from confirming that a denotational semantics defines denotations
which satisfy some expected equivalences at least for some terms,
some of the tests also depend on rewrite rules for the [postulated properties].
The success of those tests indirectly checks that the rewrite rules preserve denotations.
(A more systematic approach would be to develop a suite of unit tests for consequences
of postulated properties, independently of denotational definitions.)

[Postulated Properties]: ../Properties.md#postulated-properties


```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

import Tests.LC
import Tests.PCF
import Tests.Scm
--"/hide"
```