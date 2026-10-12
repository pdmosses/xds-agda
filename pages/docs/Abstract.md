# Abstract

Mechanisation of a mathematical definition (also referred to as formalisation)
has many benefits. Here, we focus on mechanising denotational semantic definitions
of programming languages by embedding them in the Agda language. The Agda
type-checker detects and reports any issues with the wellformedness and type
correctness of the embedded definitions.

To minimise the effort required, and to facilitate correlation of the original
definition with its Agda embedding, mechanisation should not involve significant
reformulation or extension. Here, we show how  to embed conventional Scott–Strachey
denotational definitions in Agda with almost no changes to $\lambda$-notation or
domain equations.

Agda notation for definitions of types and functions corresponds closely
to the conventional meta-notation of denotational semantics. We have developed
a collection of Agda modules with postulated types for commonly used domain
constructors and their associated operations. 

We illustrate our approach with mechanisations of three denotational definitions:
a model of the untyped $\lambda$-calculus, Plotkin’s denotational
semantics of PCF, and a semantics of a sublanguage of Scheme. In previous work,
similar mechanisations in Agda have revealed several unsuspected wellformedness
issues in published denotational definitions.

Some of the postulated properties of our definitions are inconsistent with a
classical set-theoretic interpretation of Agda. We conjecture that they would be
consistent with an interpretation of Agda in a higher-order intuititionistic logic,
such as that used by Simpson in his work on synthetic domain theory. After recalling
previous work on mechanising domain theory, we consider the possibility of
mechanising synthetic domain theory in Agda.
