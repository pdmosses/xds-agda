# Untyped Lambda-Calculus

This section presents our Agda embedding of a denotational semantics of an untyped $\lambda$-calculus.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

module Examples.LC where

  import Examples.LC.Abstract-Syntax
  import Examples.LC.Domain-Equations
  import Examples.LC.Semantic-Functions
--"/hide"
```
