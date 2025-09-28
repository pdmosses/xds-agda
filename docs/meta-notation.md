# Meta-notation

The current examples of denotational semantics given here
(untyped [lambda-calculus], [PCF], and a simple sublanguage [Scm] of Scheme)
use a lightweight shallow embedding of domain theory in Agda.

For an introduction to the Agda language, see the [Agda docs] or the
[Agda Wikipedia page].

## Summary

### Abstract Syntax

The context-free grammars conventionally used to specify abstract syntax in
denotational semantics correspond to inductive datatype definitions in Agda,
introduced by the keyword **`data`**.

For mutually-recursive definitions, all the datatypes are declared before declaring
their constructors.

In Agda, constructors with multiple arguments are curried.
Mixfix notation uses underscores to indicate argument positions.
However:

- layout characters are not allowed in mixfix names;
- underscores need to be separated by name parts;
- the characters **`.;{}()@"`** cannot be used at all; and
- the symbols **`= | -> → : ? \ λ ∀ .. ...`** and Agda keywords cannot be used as name parts.

Unicode characters can be used to suggest the terminal symbols of the specified
language, e.g., the blank character **`␣`** for a space,
and so-called banana-brackets **`⦅ ⦆`** for parentheses.

Agda doesn't allow empty mixfix names:
injections between (data)types need to be explicit.

In Agda, a value is left unspecified by declaring it either as a postulate
or as a module parameter.

### Domain Equations

A flat domain is defined by equating it to a lifted set,
which is written **`S +⊥`** in Agda.

Non-recursive groups of domains are defined by equating them to domain terms.
The currently available domain constructors are:

- **`D → E`**, the domain of functions from **`D`** to **`E`**;
- **`𝕃 D`**, lifting **`D`** with a further **`⊥`**;
- **`D × E`**, Cartesian product;
- **`D + E`**, separated sum;
- **`D ⋆`**, finite sequences.

Most of the above constructors can also be used with predomains;
and **`P → D`** is a domain also when **`P`** is a predomain.

In conventional denotational semantics, (groups of mutually) recursive domains
are defined, up to isomorphism, by domain equations. The isomorphisms between
domains and their definitions are usually left implicit.

In Agda, such isomorphisms need to be specified explicitly -- both when defining
domains and when defining elements of domains in λ-notation. See the
[lambda-calculus] semantics for an example of this.

When recursively-defined domains involve domain sums, however, the required
isomorphisms can be subsumed by postulating projections and injections between
domains and their summands. See the [Scm] semantics for an example.

The [PCF] semantics does not involve recursively-defined domains.

### Semantic Functions

Declarations and definitions of semantic functions that map abstract syntax to
domains of denotations are defined straightforwardly in Agda, by specifying
the same 'semantic equations' as in conventional denotational semantics.
Mixfix notation (e.g., **`ℰ⟦_⟧`**) supports the use of double square brackets
to separate abstract syntax from λ-notation.

Compositionality of denotational semantics ensures that the definitions of
semantic functions are inductive (primitive recursive).
Agda checks that the semantic equations cover all abstract syntax constructors,
and warns about any overlapping equations.

### Auxiliary Functions

Conventional denotational semantic definitions often define auxiliary functions
for use when defining denotations in semantic equations.
These look the same in Agda, except that recursive definitions generally need
to be formulated using the fixed-point operator **`fix`** to satisfy the Agda
termination check.

Auxiliary functions need to be declared before they are first used, so their
declarations should precede the definitions of semantic functions.

### λ-Notation

In conventional denotational semantics, functions defined in λ-notation between
domains are always continuous.
In Agda, it is possible to postulate that all functions are continuous.
Some Agda functions (e.g., Boolean negation) clearly have no fixed points,
so such postulates are inconsistent with the standard Agda library.
However, fixed points of *arbitrary* functions are not needed when defining
denotations in Agda, and it appears that such inconsistent postulates do not
affect Agda's type-checker.

Denotations can therefore be defined in Agda quite straightforwardly.
Apart from the fixed-point operator **`fix`**, definitions in λ-notation can
also use the introduction and elimination operators associated with the various
domain constructors.

Regarding lexical structure, the conventional notation for λ-abstractions
**`λx.y`** is written **`λ x → y`** in Agda, and adjacent bound variables need
to be separated by spaces.

### Modules

Currently, the examples of denotational definitions presented here are
independent, and there is some duplication of declarations of notation for
domains.

In a future version, all the domain notation should be specified in a separate
module, with submodules for the various domain constructors.

[Agda docs]: https://agda.readthedocs.io/en/v2.7.0.1/getting-started/a-taste-of-agda.html
[Agda Wikipedia page]: https://en.wikipedia.org/wiki/Agda_(programming_language)
[Lambda-calculus]: LC.md
[PCF]: PCF.md
[Scm]: Scm.md