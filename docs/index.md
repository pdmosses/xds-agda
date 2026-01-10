# About

> Experiments with Agda support for Scott–Strachey denotational semantics

## Examples

Complete examples of denotational semantics definitions in Agda:

- [LC](LC.md): the untyped λ-calculus
- [Scm](Scm.md): a sublanguage of [Scheme]

!!! info

    This website version was deployed from the `dev` branch of the repository

## Domains in Denotational Semantics

In the Scott–Strachey style of denotational semantics:

- types of denotations are (Scott-)domains;
- domains are cpos with least elements, and can be defined recursively;
- denotations are defined in λ-notation, and functions are continuous;
- the isomorphisms between domains and their definitions are left implicit.

## Domains in Agda

In Agda, the [DomainTheory] modules from the [TypeTopology] library provide
well-developed support for domains.

- Domains `D` are tuples `(⟪D⟫, ⊥, _⊑_, axioms)` where:
  
  - `⟪D⟫` is a type of elements,
  - `⊥` is a distinguished element of `⟪D⟫`,
  - `_⊑_` is a partial order on `⟪D⟫`, and
  - `axioms` prove that `(⟪D⟫, _⊑_)` is a directed-complete poset (dcpo)
    with `⊥` least.

- Continuous functions `c` from domain `D` to domain `E`  are pairs
  `(f, axioms)` where:

  - `f` is an underlying function from `⟪D⟫` to `⟪E⟫`, and
  - `axioms` prove that `f` preserves limits of directed sets.

- Domains are defined recursively as bilimits of diagrams.

- Elements of domains are defined in λ-notation, where:

  - λ-abstractions need to be paired with continuity proofs,
  - applications need to select the underlying functions, and
  - the isomorphisms between domains and their definitions are explicit.

  Such requirements give significant pragmatic issues: explicit continuity
  proofs are generally tedious to formulate (and subsequently read); and the
  notation for pairing and selection prevents direct embedding in Agda of
  λ-notation from denotational definitions.

## Extending Agda with Scott-Domains

The purpose of this repository is to experiment with extending Agda to allow
denotational semantics to be defined more straightforwardly.

The current examples presented here illustrate how denotational semantics can
be defined in Agda.
However, they use *postulates* to allow Agda to type-check the definitions,
and some of the postulates are inconsistent with the underlying Agda logic.
This does not affect type-checking, but could lead to unsound equivalence proofs.

### Adding a Universe of Domains

One idea is to distinguish between declarations of types that correspond
to domains and declarations of ordinary types – e.g., by introducing a universe
(hierarchy) for domains.

A domain type would implicitly be a cpo, with built-in notation for its partial
order and least element. A type that corresponds to the domain of continuous 
functions from a domain to itself would also have a least fixed-point function.

### Implementing Synthetic Domain Theory

An implementation of Synthetic Domain Theory (SDT) in Agda would address the
pragmatic issues with using the [DomainTheory] modules from the [TypeTopology]
library.

From the abstract of [Formalizing Synthetic Domain Theory] by Bernhard Reus
(J. Automated Reasoning, 1999):

> Synthetic Domain Theory (SDT) is a constructive variant of Domain Theory
> where all functions are continuous following Dana Scott’s idea of
> “domains as sets”.
> 
> In this article a logical and axiomatic version of SDT capturing the essence
> of Domain Theory à la Scott is presented. It is based on a sufficiently
> expressive version of constructive type theory and fully implemented in the
> proof checker [Lego].

It appears that the implementation uses impredicativity and proof-irrelevance,
which may prevent migration to Agda.

From the abstract of
[Computational adequacy for recursive types in models of intuitionistic set theory]
by Alex Simpson (Ann. Pure and Applied Logic, 2004):

> This paper provides a unifying axiomatic account of the interpretation of
> recursive types that incorporates both domain-theoretic and realizability
> models as concrete instances. Our approach is to view such models as full
> subcategories of categorical models of intuitionistic set theory. 

From §3:

> Although in this paper we use models of IZF set theory to achieve algebraic
> compactness, many other set theories and type theories appear rich enough to
> carry out the proofs in this paper. ... In fact, it seems likely that, with
> appropriate reformulations, the development of this paper could be carried
> out in the (predicative) context of Martin-Löf’s Type Theory.

It remains to be seen whether the development can be implemented in Agda...

## Discussion

Advice and suggestions are welcome, e.g., by posting to the repo [Discussions].

Peter Mosses <p.d.mosses@tudelft.nl>

[Scheme]: https://scheme.org
[DomainTheory]: https://martinescardo.github.io/TypeTopology/DomainTheory.index.html "Agda modules"
[TypeTopology]: https://martinescardo.github.io/TypeTopology/ "Agda library"
[DomainTheory.Bilimits.Dinfinity]: https://martinescardo.github.io/TypeTopology/DomainTheory.Bilimits.Dinfinity.html  "Agda module"
[Formalizing Synthetic Domain Theory]: https://doi.org/10.1023/A:1006258506401 "JAR paper DOI"
[Lego]: https://www.dcs.ed.ac.uk/home/lego/ "Web page"
[Computational adequacy for recursive types in models of intuitionistic set theory]: https://doi.org/10.1016/j.apal.2003.12.005 "APAL paper DOI"
[Discussions]: https://github.com/pdmosses/xds-agda/discussions