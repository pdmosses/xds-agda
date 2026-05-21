# *Scm*: A Sublanguage of *Scheme*

*Scm* is a particularly basic sublanguage of the core *Scheme* expression language
whose denotational semantics is defined in the *Scheme* reports [(Scheme)].
The domains and auxiliary functions declared in this section are explained
in the presentation of the conventional denotational semantics of *Scm* [(Mosses2025CSE)];
they involve the notation for [sequence domains].

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.Scm where

import Examples.Scm.Abstract-Syntax
import Examples.Scm.Domain-Equations
import Examples.Scm.Semantic-Functions
import Examples.Scm.Auxiliary-Functions
--"/hide"
```

[Sequence Domains]: ../../Notation.md#sequences
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Scheme)]: https://standards.scheme.org