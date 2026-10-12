# Denotational Semantics

## Features

A denotational semantic description of a programming language specifies
*abstract syntax*, *semantic domains*, and *semantic functions*.

Abstract syntax.
:   An abstract syntax defines semantically-relevant sets of phrases
    (e.g., commands, declarations, expressions) and their compositional structure.
    Phrases are regarded as *abstract syntax trees* (ASTs), rather than as strings of symbols.

    Abstract syntax is specified by a *context-free grammar*.
    The nonterminal symbols of the grammar correspond to named sets of ASTs.
    BNF-like productions determine notation for AST node constructors.

Semantic domains.
:   The *denotation* of a phrase models the contribution of that phrase
    to the semantics of all programs in which it occurs.
    Semantic domains are sets of abstract mathematical values (e.g., functions, tuples, truth values)
    used to construct denotations.

    Semantic domains are specified by *domain equations* that define named semantic domains
    in terms of standard *domain constructors*.
    The definitions can be (mutually) recursive.

Semantic functions.
:   These functions map abstract phrases to their denotations.
    They are required to be *compositional*:
    the denotation of a phrase generally depends on the denotations of its sub-phrases,
    but it cannot depend on their syntax.

    Semantic functions are specified inductively by *semantic equations*.
    Their AST arguments are enclosed by $\llbracket\dots\rrbracket$,
    avoiding potential confusion between notation for AST constructors and elements of domains.

## Domain Notation

Domains were originally required to be *continuous lattices*
[(Scott1970OMT)]\ [(Scott1972CL)]\ [(Stoy1977DSS)]\ [(Tennent1976DSP)].
Various more general notions of domain have been suggested (e.g., see [(Abramsky1995DT)])
but here it is only important that endofunctions between domains have *fixed points*,
recursive *domain equations* have well-defined solutions (up to isomorphism),
and each domain comes with a *bottom element*.
The conventional notation for domain constructors and their accompanying operations,
summarised below, is independent of the exact notion of domain.

Domains.
:   Every domain $D$ has a *bottom* element $\bot_D$ that represents
    absence of information (e.g., due to an error or nontermination of a
    computation), usually written just $\bot$.

Function domains.
:   A function $\phi : D \to E$ is (Scott-)*continuous* if it is monotone and
    preserves limits of directed subsets of\ $D$\ [(Abramsky1995DT)].
    The *function domain* $F = D \to E$ consists of all continuous (total) functions from $D$ to $E$.
    The set of all functions from a set\ $A$ to a domain also forms a domain, ordered pointwise.

    Functions between domains are always continuous when they are defined only using
    abstraction (written $\lambda \delta.\epsilon$),
    application (written $\phi\,\delta$),
    the operation $\textit{fix}$ that maps each endofunction $\phi : D \to D$ to its least fixed point,
    and the continuous operations associated with other domain constructors.

Flat domains.
:   For any set $A$ the *flat domain* $A_\bot$ is formed by adding $\bot$ as a fresh element.
    Functions on sets are implicitly extended to (continuous) functions on flat domains,
    returning\ $\bot$ when any argument is\ $\bot$.

    Elements\ $\tau$ of the domain of *truth-values* $\textbf{T} = \{ \textit{true}, \textit{false} \}_\bot$
    are used in *conditionals* written $\tau \to \delta_1, \delta_2\,$,
    where $\delta_1, \delta_2 : D$, $\textit{true} \to \delta_1, \delta_2$ is $\delta_1\,$,
    $\textit{false} \to \delta_1, \delta_2$ is $\delta_2\,$, and
    $\bot_{\textbf{T}} \to \delta_1, \delta_2$ is $\bot_D\,$.

Sum domains.
:   The *separated sum domain* $X = \ldots + Y + \ldots$ consists of injected elements
    written '$\upsilon \textsf{ in } X$' (where $\upsilon : Y$ for some summand $Y$)
    together with $\bot_X$.

    The $\textbf{T}$-valued operation $\chi \mathbin{\textsf{E}} Y$
    (written $\chi \in Y$ in [(Scheme)])
    tests whether $\chi : X$ is the injection of some $\upsilon : Y$;
    if so, $\chi \mid Y$ projects $\chi$ to $\upsilon$, otherwise to $\bot_X$.
    (This notation has the pragmatic advantage of being independent of the order of the summands.)

Product domains.
:   The *product domain* $P = D \times E$ consists of pairs written $\langle \delta, \epsilon \rangle$,
    where $\delta : D$, $\epsilon : E$, and $\bot_P = \langle \bot_D, \bot_E \rangle$.
    When $\pi : P$, the operations $\pi \downarrow 1$ and $\pi \downarrow 2$ select its components.

    The domain of $n$-*tuples* $\langle \delta_1, \ldots, \delta_n \rangle$ of elements $\delta_i : D$
    is written\ $D^n$, and the domain of all finite *sequences* is written\ $D^*$.
    Further operations on\ $D^*$ include the empty sequence\ $\langle \rangle$,
    concatenation\ $\delta^*_1 \mathbin{\S} \delta^*_2$, length\ $\textit{\#}\,\delta^*$,
    $n$th\ component $\delta^* \downarrow n$, and $n$th\ tail $\delta^* \mathbin{\dagger} n$ ($n \geq 1$).

Recursive domains.
:   In a collection of domain equations $D_i = E_i$, the $D_i$ are distinct domain names,
    and the $E_i$ are domain terms formed from standard domain constructors and domain names,
    allowing unrestricted recursion.
    However, the solution of the equations is only up to an isomorphism
    (written $\textit{unfold} : D_i \to E_i$\ , $\textit{fold} : E_i \to D_i$ in [(Abramsky1995DT)],
    and $\phi : D_i \to E_i$\ , $\psi : E_i \to D_i$ in [(Reynolds1998TPL)],
    but usually left implicit).

Updates.
:   The *update* $\phi[\epsilon / \delta]$ of a function $\phi : D \to E$ 
    maps (non-$\bot$) $\delta : D$ to $\epsilon : E$,
    and all other elements $\delta' : D$ to $\phi(\delta')$.
    The domain $D$ has to be flat (with a continuous equality);
    the same notation is used when $D$ is a set.
```agda
--"hide"
module Background.Denotational-Semantics where
--"/hide"
```

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Reynolds1998TPL)]: https://doi.org/10.1017/CBO9780511626364
[(Scheme)]: https://standards.scheme.org
[(Scott1970OMT)]: https://ncatlab.org/nlab/files/Scott-TheoryOfComputation.pdf
[(Scott1972CL)]: https://doi.org/10.1007/BFb0073967
[(Stoy1977DSS)]: https://mitpress.mit.edu/9780262690768/denotational-semantics/
[(Tennent1976DSP)]: https://doi.org/10.1145/360303.360308