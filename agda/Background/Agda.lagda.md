# Agda

## Features

Agda [(Agda-Language)]\ [(Agda-Wikipedia)] is both a strongly typed
functional *programming language* with support for first-class
*dependent types* and a *proof assistant* based on the Curry–Howard
correspondence between propositions and types. A number of features set
Agda apart from a typical functional programming language:

- Types in Agda are first-class values of a *universe* $\textsf{Set}_i$ where
  $\textsf{Set} = \textsf{Set}_0$, and each universe $\textsf{Set}_i$
  belongs to the next universe $\textsf{Set}_{i+1}$.

- Agda has *dependent function types* `(x : A) → B` or `∀ x → B`
  where the type `B` can depend on the value `x`.

- All functions in Agda are *total*: evaluating a function call is
  guaranteed to return a value of the correct type in finite time. To
  ensure totality, Agda's type checker includes a termination check for
  recursive definitions, a positivity check for inductive datatypes, and
  a consistency check for universe levels.

Thanks to its dependent types and totality, Agda's type system can be
used as a higher-order logic for writing mathematical statements and
proofs, where types correspond to propositions and type checking
corresponds to checking the validity of the proof.

## Agda Syntax

The following syntactic constructs are used in our Agda code.

Comments.
:   End-of-line comments are initiated by `--`, while multi-line comments
    are between `{-` and `-}`.

Naming.
:   Declared symbols, variables, and type constructors all share a
    single namespace. Names can be any sequence of non-whitespace ASCII
    and Unicode characters except `.;{}()@"`, excluding reserved symbols
    and keywords such as `→` or `where`. Underscores in names play a special role
    for mixfix notation.

Mixfix notation.
:   Agda supports *mixfix notation* for defining operators, with
    underscores in the name of a symbol indicating argument positions.
    For example, if we declare `_+_ : Nat → Nat → Nat`,
    we can use it as `1 + 1` (the spaces are required, since `1+1` is a valid Agda name!).

Anonymous functions.
:   Lambda abstractions use the syntax `λ x → u` instead of `λ x. u`.

Implicit arguments.
:   Arguments marked by single curly braces `{…}` in the type of a symbol are
    considered to be *implicit*. These arguments may be omitted, and are
    then inferred by Agda's type checker.

Type classes.
:   Agda has no direct support for type classes, but they can be
    simulated using Agda's *instance arguments* to resolve type class
    instances. Instance arguments are marked by double curly braces `{{…}}` and
    are resolved automatically by using definitions marked as `instance`.

Rewrite rules.
:   Agda has support for *rewrite rules* [(Cockx2020TTU)]
    that are applied automatically during type checking. Rewrite rules
    are declared by marking an equality proof 
    `eq : a ≡ b` with a `{-# REWRITE eq #-}` pragma. Agda can
    optionally check confluence of rewrite rules, but currently does not
    check their termination. Since only *proven* (or postulated)
    equalities can be added as rewrite rules, non-confluence and
    non-termination cannot affect the soundness of Agda's type checker,
    only its completeness [(Cockx2021TRT)].
```agda
--"hide"
module Background.Agda where
--"/hide"
```

[(Agda-Language)]: https://agda.readthedocs.io/en/v2.8.0/language/
[(Agda-Wikipedia)]: https://en.wikipedia.org/wiki/Agda_(programming_language)
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
[(Cockx2020TTU)]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2019.2
