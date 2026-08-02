# Illustrative Examples

This section illustrates mechanisation of denotational semantics in Agda
with three examples, all using the [postulated notation] for domains and their
associated operations:
the [Untyped Lambda-Calculus],
[PCF: A Programming Language for Computable Functions], and
[*Scm*: A Sublanguage of *Scheme*].
```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples where

import Examples.LC
import Examples.PCF
import Examples.Scm
```

[Postulated Notation]: ../Notation.md#postulated-domain-notation
[Untyped Lambda-Calculus]: ../Examples/LC/index.md#untyped-lambda-calculus
[PCF: A Programming Language for Computable Functions]: ../Examples/PCF/index.md#pcf-a-programming-language-for-computable-functions
[*Scm*: A Sublanguage of *Scheme*]: ../Examples/Scm/index.md#scm-a-sublanguage-of-scheme