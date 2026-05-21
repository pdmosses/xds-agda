# Background

## Denotational Semantics

A conventional Scott–Strachey denotational semantics of a programming language consists of
definitions of *abstract syntax*, *semantic domains*, and *semantic functions*.
The abstract syntax uses a *context-free grammar* to define sets of abstract syntax trees (ASTs)
that model the compositional structure of programs and their phrases.
The semantic domains are defined by equations in terms of *domain constructors*,
and can be mutually recursive.
The semantic functions are defined *inductively*, also with mutual recursion,
and map ASTs to their *denotations*, which are elements of domains.
The denotation of an AST models its contribution to the semantics of complete programs,
and is defined *compositionally* in terms of the denotations of its direct components.
The AST arguments of semantic functions are enclosed by $\llbracket\dots\rrbracket$,
to avoid potential confusion between abstract syntax terms and semantic notation.

Domains were originally required to be continuous lattices [(Scott1970OMT)]\ [(Scott1972CL)]\ [(Stoy1977DSS)]\ [(Tennent1976DSP)].
Various more general notions of domain have been suggested (see [(Abramsky1995DT)])
but for us it is only important that endomaps between domains have fixpoints,
recursive domain equations have solutions, and each domain comes with a bottom element.
The notation for domain constructors and their accompanying operations in a conventional Scott–Strachey semantics, 
summarised below, is independent of the choice of domains.

Let $D, E$ be domains with elements $\delta : D$, $\epsilon : E$.

- Every domain $D$ has a *bottom* element $\bot_D$ that represents
  absence of information (e.g., due to an error or nontermination of a
  computation), usually written just $\bot$.

- A function $\phi : D \to E$ is (Scott-) *continuous* if it is monotone and
  preserves limits of directed subsets of\ $D$\ [(Abramsky1995DT)].
  The *function domain* $F = D \to E$ consists of all continuous (total) functions from $D$ to $E$.
  The set of all functions from a set\ $A$ to a domain also forms a domain, ordered pointwise.
  Functions between domains are defined using abstraction $\lambda \delta.\epsilon$, application $\phi\,\delta$,
  the operation $\texttt{fix}$ that maps each endofunction $\phi : D \to D$ to its least fixed point,
  and the operations associated with other domain constructors.

- For any set $A$ the *flat domain* $A_\bot$ is formed by adding $\bot$ as a fresh element.
  Functions on sets are implicitly extended to (continuous) functions on flat domains,
  returning\ $\bot$ when any argument is\ $\bot$.
  Elements\ $\tau$ of the domain of *truth-values* $\textbf{T} = \{ \text{true}, \text{false} \}_\bot$
  are used in *conditionals* written $\tau \to \delta_1, \delta_2$,
  where $\text{true} \to \delta_1, \delta_2$ is $\delta_1$,
  $\text{false} \to \delta_1, \delta_2$ is $\delta_2$, and
  $\bot_{\textbf{T}} \to \delta_1, \delta_2$ is $\bot_D$.

- The *separated sum domain* $X = \ldots + Y + \ldots$ consists of injected elements
  written '$\upsilon \textsf{ in } X$' (where $\upsilon : Y$ for some summand $Y$)
  together with $\bot_X$.
  The $\textbf{T}$-valued operation $\chi \mathbin{\textsf{E}} Y$
  (written $\chi \in Y$ in [(Scheme)])
  tests whether $\chi : X$ is the injection of some $\upsilon : Y$;
  if so, $\chi \mid Y$ projects $\chi$ to $\upsilon$, otherwise to $\bot_Y$.

- The *product domain* $P = D \times E$ consists of pairs
  $\langle \delta, \epsilon \rangle$ with
  $\bot_P = \langle \bot_D, \bot_E \rangle$. When $\pi : P$,
  the operations $\pi \downarrow 1$ and $\pi \downarrow 2$ select its components;
  similarly for domains of $n$-*tuples*\ $D^n$ and finite *sequences*\ $D^*$.
  Further operations on\ $D^*$ include the empty sequence\ $\langle \rangle$,
  concatenation\ $\delta^*_1 \mathbin{\S} \delta^*_2$, length\ $\text{\#}\,\delta^*$,
  $n$th\ component $\delta^* \downarrow n$, and $n$th\ tail $\delta^* \mathbin{\dagger} n$ ($n \geq 1$).

Robert Tennent's highly accessible tutorial on denotational semantics\ [(Tennent1976DSP)]
includes illustrative examples using the above notation (partly in continuation-passing style)
and further details of the conventional Scott–Strachey style.

## Agda

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

### Notes on some of Agda's syntax and features {-}

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

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Agda-Language)]: https://agda.readthedocs.io/en/v2.8.0/language/
[(Agda-Wikipedia)]: https://en.wikipedia.org/wiki/Agda_(programming_language)
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
[(Cockx2020TTU)]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2019.2
[(Scheme)]: https://standards.scheme.org
[(Scott1970OMT)]: https://ncatlab.org/nlab/files/Scott-TheoryOfComputation.pdf
[(Scott1972CL)]: https://doi.org/10.1007/BFb0073967
[(Stoy1977DSS)]: https://mitpress.mit.edu/9780262690768/denotational-semantics/
[(Tennent1976DSP)]: https://doi.org/10.1145/360303.360308