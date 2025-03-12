# Meta-notation

This page summarises the current representation of conventional Scott--Strachey
style denotational semantics meta-notation in Agda.

For an introduction to the Agda language, see the [Agda docs] or the
[Agda Wikipedia page]. 

## Abstract Syntax

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

A type can be left unspecified by declaring it as a postulate
(or a module parameter) in Agda.

## Domain Equations

A flat domain is defined by equating it to a lifted set,
which is written **`S +⊥`** or **`𝕃 S`** in Agda.

Non-recursive groups of domains are defined by equating them to domain terms.
The currently available domain constructors are:

- **`D → E`**, the domain of functions from **`D`** to **`E`**;
- **`𝕃 D`**, lifting **`D`** with a further **`⊥`**;
- **`D × E`**, Cartesian product;
- **`𝕃 (D + E)`**, separated sum;
- **`D ⋆`**, finite sequences: **`𝕃 ((D ^ 0) + ... + (D ^ n) + ...)`**.

Most of the above constructors can also be used with predomains;
and **`P → D`** is a domain also when **`P`** is a predomain.
(Domain sequences use a superscript asterisk **`D ⋆`**, whereas
predomain sequences use a plain asterisk **`P *`**.)

(Groups of mutually) recursive domains are defined by first postulating each
name to be of type **`Domain`**, then postulating *instances* of propositions
of the form **`iso-D : D ↔ E`** asserting that the domain named **`D`** is
isomorphic to the domain **`E`** formed from domain constructors and names.
The special Agda module application **`open Function.Inverse {{ ... }}`**
then declares the inverse functions **`to : D → E`** and **`from : E → D`**
for each declared isomorphism.

In conventional denotational semantics, definitions of domains are simply
specified as equations, and the isomorphisms between domains and their
definitions are left implicit.
The isomorphisms need to be specified explicitly in Agda -- both when defining
domains and when defining elements of domains in λ-notation.

## Semantic Functions

Declarations and definitions of semantic functions that map abstract syntax to
domains of denotations are defined straightforwardly in Agda, by specifying
the same 'semantic equations' as in conventional denotational semantics.
Mixfix notation (e.g., **`ℰ⟦_⟧`**) supports the use of double square brackets
to separate abstract syntax from λ-notation.

Compositionality of denotational semantics ensures that the definitions of
semantic functions are inductive (primitive recursive).
Agda checks that the semantic equations cover all abstract syntax constructors,
and warns about any overlapping equations.

## Auxiliary Functions

Conventional denotational semantic definitions often define auxiliary functions
for use when defining denotations in semantic equations.
These look the same in Agda, except that recursive definitions generally need
to be formulated using the fixed-point operator **`fix`** to satisfy the Agda
termination check.

Auxiliary functions need to be declared before they are first used, so their
declarations should precede the definitions of semantic functions.

## λ-Notation

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

## Modules

Currently, the examples of denotational definitions presented here are
independent, and there is some duplication of declarations of notation for
domains.
In a future version, all the domain notation should be specified in a separate
module, with submodules for the various domain constructors.

[Agda docs]: https://agda.readthedocs.io/en/v2.7.0.1/getting-started/a-taste-of-agda.html
[Agda Wikipedia page]: https://en.wikipedia.org/wiki/Agda_(programming_language)