# Postulated Domain Notation

This section postulates Agda notation for the domain constructors and
associated functions used in the [illustrative examples].

@latex
See the accompanying repository and the generated website [(MFPS2026-Agda)]
for the complete Agda code with the details elided here (including most module
imports, fixity declarations, and declarations of the types of meta-variables).
@/latex

The Agda code that declares our embedding of domain notation is divided into
the modules imported below:

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation where
  import Notation.Domains
  import Notation.Functions
  import Notation.Flat
  import Notation.Flat.Booleans
  import Notation.Flat.Naturals
  import Notation.Sums
  import Notation.Products
  import Notation.Products.Tuples
  import Notation.Products.Sequences
  import Notation.Recursion
  import Notation.Updates
```

@latex
In the PDF of this paper, Agda code blocks are highlighted, but in general,
names are *not* hyperlinked to their declarations.
However, each declared or referenced *module name*
is hyperlinked to the declaration of that module in the website,
to facilitate browsing the Agda code when online.
@/latex

[Illustrative Examples]: ../Examples/index.md#illustrative-examples
[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
