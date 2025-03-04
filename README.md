# Denotational Semantics in Agda

> Experiments with Agda support for Scott–Strachey denotational semantics.

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

## Example: PCF

> PCF is a call-by-name simply-typed λ-calculus equipped with one or two base
> types (usually natural numbers and Booleans) and a fixed point combinator.
> In essence, PCF is the simplest lazy, purely functional programming language.
> ([PLS Lab])

PCF and its denotational semantics were orginally defined by Dana Scott in 1969
([Scott 1993]) including combinators (`S`, `K`) instead of λ-abstraction.
Gordon Plotkin subsequently defined a denotational semantics for PCF including 
λ-abstraction ([Plotkin 1977]).

A direct transcription of Plotkin's definition to Agda is available in this
repo at [PCF.All] (see also the [generated PDF][Generated PDF of PCF]).
The code imports various modules from the [standard Agda library v2.1], and
typechecks with Agda v2.6.4.3 using the (blatantly unsafe) workarounds and
postulates in the [Domain-Notation][PCF Domain-Notation] module.

Many authors have defined denotational semantics for PCF ([PLS Lab]). Recently,
Tom de Jong has given a definition in Agda ([DomainTheory.ScottModelOfPCF])
based on the [DomainTheory] modules from the [TypeTopology] library. The syntax
follows ([Scott 1993]) by including combinators instead of λ-abstraction.

De Jong's semantics of PCF was extended to PCF with variables and λ-abstraction
by Brendan Hart in a final year project supervised by Martín Escardó and
De Jong ([Hart 2020]).[^1] Hart used De Bruin indices for variables.

[^1]: Both De Jong and Hart deviate slightly from Scott's original semantics
    of the predecessor function by defining it to return zero when applied to
    zero, instead of being undefined.

The definitions of the denotations of PCF terms given by De Jong and Hart
illustrate the notational overhead that arises in Agda formalizations when
using the [DomainTheory] modules, compared to the original definitions given by
Scott and Plotkin.

## Example: Untyped λ-Calculus

De Jong has also given an example of how to define a domain recursively,
as needed for the denotational semantics of the untyped λ-calculus, see
[DomainTheory.Bilimits.Dinfinity].

A definition in Agda is available in this repo at [ULC.All] (see also the
[generated PDF][Generated PDF of ULC]).

## Extending Agda with Scott-Domains

The purpose of this repo is to experiment with techniques to allow
denotational semantics to be defined more straightforwardly in Agda.

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

[PLS Lab]: https://www.pls-lab.org/PCF "Web page"
[Scott 1993]: https://doi.org/10.1016/0304-3975(93)90095-B "TCS paper DOI"
[Plotkin 1977]: https://doi.org/10.1016/0304-3975(77)90044-5 "TCS paper DOI"
[PCF.All]: https://github.com/pdmosses/xds-agda/blob/main/PCF/All.lagda "Agda module"
[Generated PDF of PCF]: https://github.com/pdmosses/xds-agda/blob/main/latex/PCF.pdf "PDF generated by Agda"
[PCF Domain-Notation]: https://github.com/pdmosses/xds-agda/blob/main/PCF/Domain-Notation.lagda "Agda module"
[ULC.All]: https://github.com/pdmosses/xds-agda/blob/main/ULC/All.lagda "Agda module"
[Generated PDF of ULC]: https://github.com/pdmosses/xds-agda/blob/main/latex/ULC.pdf "PDF generated by Agda"
[ULC Domains]: https://github.com/pdmosses/xds-agda/blob/main/ULC/Domains.lagda "Agda module"
[standard Agda library version 2.1]: https://agda.github.io/agda-stdlib/v2.1 "Agda library"
[DomainTheory]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.index.html "Agda modules"
[TypeTopology]: https://www.cs.bham.ac.uk/~mhe/TypeTopology "Agda library"
[DomainTheory.ScottModelOfPCF]: https://martinescardo.github.io/TypeTopology/DomainTheory.ScottModelOfPCF.ScottModelOfPCF.html "Agda module"
[Hart 2020]: https://github.com/BrendanHart/Investigating-Properties-of-PCF "GitHub repo"
[DomainTheory.Bilimits.Dinfinity]: https://martinescardo.github.io/TypeTopology/DomainTheory.Bilimits.Dinfinity.html  "Agda module"
[Formalizing Synthetic Domain Theory]: https://doi.org/10.1023/A:1006258506401 "JAR paper DOI"
[Lego]: https://www.dcs.ed.ac.uk/home/lego/ "Web page"
[Computational adequacy for recursive types in models of intuitionistic set theory]: https://doi.org/10.1016/j.apal.2003.12.005 "APAL paper DOI"
[Discussions]: https://github.com/pdmosses/xds-agda/discussions