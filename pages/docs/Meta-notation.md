# Meta-notation

The current examples of denotational semantics given here use a lightweight
shallow embedding of Scott-domains in Agda. The module [Notation] postulates
the required domain constructors and their associated operations.

## Summary

The [Background] section includes an overview of the main Agda features used here.

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

Agda doesn't allow empty mixfix names: injections between (data)types need to
be explicit.

In Agda, a value is left *unspecified* by declaring it either as a **postulate**
or as a module parameter.

### Domain Equations

An Agda type `Domain` of domains is postulated. Each domain `D` has a
*carrier* set, written `⟪ D ⟫`, and a distinguished element `⊥`.
The detailed mathematical structure of domains does not affect the formulation
of a denotational semantics, and is left unspecified.

Non-recursive groups of domains are defined by equating them to domain terms.
The currently available domain constructors are:

- **`D →ᶜ E`**, the domain of (supposedly continuous) functions from a domain
  **`D`** to a domain **`E`**;
- **`A →ˢ D`**, the domain of *all* functions from a set **`A`** to a domain
  **`D`**;
- **`A +⊥`**. the flat domain constructed by adding `⊥`to a set **`A`**;
- **`D + E`**, the *separated* sum of domains **`D`** and **`E`**;
- **`D × E`**, the product of domains **`D`** and **`E`**;
- **`D ^ n`**, the domain of n-tuples of elements of a domain **`D`**;
- **`D ⋆`**, the domain of finite sequences of elements of a domain **`D`**.

In conventional denotational semantics, (groups of mutually) recursive domains
are defined, up to isomorphism, by domain equations. The isomorphisms between
domains and their definitions are usually left implicit.

Agda types can also be defined by equations, but recursion causes
non-termination of the type-checker. A recursive definition `D = E` where `E`
references `D` is formalised by postulating `D` as a domain, together with
inverse functions mapping elements of `⟪ D ⟫` to elements of `⟪ E ⟫` and
vice versa. When `E` is a separated sum domain, the inverse functions are
subsumed by postulated projections and injections between domains and their
summands. For example, see the postulated domain **E** in the module
[Examples.Scm.Domain-Equations].

### Semantic Functions

Declarations and definitions of semantic functions that map abstract syntax to
domains of denotations are defined straightforwardly in Agda, by specifying
the same 'semantic equations' as in conventional denotational semantics.
Agda's mixfix notation (e.g., **`ℰ⟦_⟧`**) supports the use of double square
brackets to separate abstract syntax from λ-notation.

Compositionality of denotational semantics ensures that the definitions of
semantic functions are inductive (primitive recursive). Agda checks that the
semantic equations cover all abstract syntax constructors, and warns about any
overlapping equations.

### Auxiliary Functions

Conventional denotational semantic definitions often define auxiliary functions
for use when defining denotations in semantic equations.
These look the same in Agda, except that recursive definitions generally need
to be formulated using the fixed-point operator **`fix`** to satisfy the Agda
termination check.

Auxiliary functions need to be declared before they are first used, so their
declarations should precede the definitions of semantic functions.

### λ-Notation

In conventional denotational semantics, functions between domains are defined in
λ-notation, and automatically continuous, which ensures that all endofunctions
on a domain `D` have (least) fixed points. Their embedding in Agda is such that
all terms of type `D →ᶜ D` are defined in λ-notation. The function **`fix`** is
postulated to map all functions in the carrier of `D →ᶜ D` to their fixed points.

Denotations can therefore be defined in Agda quite straightforwardly.
Apart from the fixed-point operator **`fix`**, definitions in λ-notation can
also use the introduction and elimination operators associated with the various
domain constructors.

Regarding lexical structure, the conventional notation for λ-abstractions
**`λx.y`** is written **`λ x → y`** in Agda, and adjacent bound variables need
to be separated by spaces.

### Modules

All the examples of denotational definitions presented here are based on
the shallow embeding of domain notation in the module [Notation], importing
its submodules for the required domain constructors.

[Agda docs]: https://agda.readthedocs.io/en/latest/getting-started/a-taste-of-agda.html
[Agda Wikipedia page]: https://en.wikipedia.org/wiki/Agda_(programming_language)
[Notation]: Notation.md
[Background]: Background.md
[Examples.Scm.Domain-Equations]: Examples/Scm/Domain-Equations.md