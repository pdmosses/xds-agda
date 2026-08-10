# Mechanising Denotational Semantics in Agda

Agda code accompanying the preliminary version of a paper ([PDF]) [presented] at [MFPS 2026]:

> Peter D. Mosses, Jesper Cockx, Bernhard Reus: *Mechanising Denotational Semantics in Agda*

[PDF]: https://ul-fmf.github.io/mfps-sstt-2026/files/pdfs/mfps/MFPS26-17.pdf
[presented]: https://ul-fmf.github.io/mfps-sstt-2026/programme/#wednesday-june-3-mfps
[MFPS 2026]: https://ul-fmf.github.io/mfps-sstt-2026/mfps/

## Navigation

On wide displays, the top panel of each page shows:

- [About] – this page, [Background], [Meta-notation]
- [Notation] – postulated types for domain constructors and associated operations
- [Examples] - embedded denotational definitions [Examples.LC], [Examples.PCF], [Examples.Scm]
- [Properties] – postulated equivalences for operations
- [Tests] - proven equivalences of denotations of [Tests.LC] and [Tests.PCF] terms
- [Library] – modules imported from the [standard Agda library] (v2.3)
- [pdmosses/xds-agda] – the code repository
- a toggle between light, dark, and automatic modes
- a earch field

The section navigation hierarchy is shown on the left.
The subsections of the current page are shown on the right.

On narrow displays, the window may show only the navigation hierarchy button 
and the search button.

The footer of each page shows links to the previous and next pages.
When scrolling up, a back to top button is shown near the top of the window.

**Agda code blocks**

- Names are links to their declarations.
- The [agda] directory contains the complete literate Agda Markdown code.
- The [docs] directory contains source code for generating the website.

## Abstract

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
constructors and their associated operations. Some of our postulates are
inconsistent with a classical set-theoretic interpretation of Agda; we conjecture
that they would be consistent with an interpretation of Agda in the higher-order
intuititionistic logic used by Simpson in his work on synthetic domain theory.

We illustrate our approach with mechanisations of three denotational definitions:
Scott’s $D_\infty$ model of the untyped $\lambda$-calculus, Plotkin’s denotational
semantics of PCF, and a semantics of a sublanguage of Scheme. In previous work,
similar mechanisations in Agda have revealed several unsuspected wellformedness
issues in published denotational definitions.

## Contributing

Please report any [issues] that you notice.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

[Issues]: https://github.com/pdmosses/xds-agda/issues
[Pull requests]: https://github.com/pdmosses/xds-agda/pulls
[Discussions]: https://github.com/pdmosses/xds-agda/discussions

[Background]: Background.md
[Meta-notation]: Meta-notation.md
[Notation]: Notation.md
[Examples]: Examples/index.md
[Examples.LC]: Examples/LC/index.md
[Examples.PCF]: Examples/PCF/index.md
[Examples.Scm]: Examples/Scm/index.md
[Properties]: Properties.md
[Tests]: Tests/index.md
[Tests.LC]: Tests/LC.md
[Tests.PCF]: Tests/PCF.md
[Library]: Library/index.md
[Standard Agda library]: https://agda.github.io/agda-stdlib/v2.3/
[pdmosses/xds-agda]: https://github.com/pdmosses/xds-agda/
[agda]: https://github.com/pdmosses/xds-agda/tree/main/agda
[docs]: https://github.com/pdmosses/xds-agda/tree/main/docs
