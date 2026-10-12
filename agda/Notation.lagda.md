# Postulated Domain Notation

This section postulates Agda notation for the domain constructors and
associated functions used in the [illustrative examples].



The Agda code that declares our embedding of domain notation is divided into
the modules imported below:

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

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



[Illustrative Examples]: ../Examples/index.md#illustrative-examples
[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
