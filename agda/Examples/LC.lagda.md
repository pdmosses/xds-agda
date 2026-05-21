# Untyped Lambda-Calculus

This section presents our Agda embedding of a denotational semantics of the untyped $\lambda$-calculus.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC where

import Examples.LC.Abstract-Syntax
import Examples.LC.Domain-Equations
import Examples.LC.Semantic-Functions
--"/hide"
```