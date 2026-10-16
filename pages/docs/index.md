# Mechanising Denotational Semantics in Agda

Agda code accompanying the **final version** of a paper [presented] at [MFPS 2026]:

> Peter D. Mosses, Jesper Cockx, Bernhard Reus: *Mechanising Denotational Semantics in Agda*

**Preprint:** <https://doi.org/10.48550/arXiv.2610.14898>

[presented]: https://ul-fmf.github.io/mfps-sstt-2026/programme/#wednesday-june-3-mfps
[MFPS 2026]: https://ul-fmf.github.io/mfps-sstt-2026/mfps/

!!! info

    The Agda code and Markdown source files used to generate this website were
    copied from the [mfps2026-agda] repository. However, there was *ad hoc*
    markup in the Agda code blocks, indicating lines that were hidden when
    including the code in the paper; here, this markup has been *removed*, to
    facilitate browsing and editing the code locally.

## Navigation

In **Agda code blocks**, clicking on a name jumps to its declaration.

When scrolling up, a **back to top** button appears.

### Wide displays

The **top panel** of each page shows a row of tabs:

- [About] – the present page, and pages summarising [Background] and [Meta-notation]
- [Notation] – postulated types for domain constructors and associated operations
- [Examples] - shallow embeddings of denotational definitions
- [Properties] – postulated equivalences for operations
- [Tests] - some proven equivalences of denotations
- [Library] – modules imported from the [standard Agda library] (v2.3)

It also shows:

- a link to the **code repository**
- a **toggle** between light, dark, and automatic modes
- a **search** field

The **left sidepanel** shows the **navigation hierarchy**. 
When there is more than one level of navigation, clicking the **expander icon**
 `>` for a section reveals links to its next level.

The **right sidepanel** shows links to any **subsections** of the current page.

### Narrow displays

The window may show only the **navigation hierarchy** button 
and the **search** button.

## Contributing

Please report any [issues] that you notice.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

[Issues]:                 https://github.com/pdmosses/xds-agda/issues
[Pull requests]:          https://github.com/pdmosses/xds-agda/pulls
[Discussions]:            https://github.com/pdmosses/xds-agda/discussions

[About]:                  index.md
[Background]:             Background/index.md
[Meta-notation]:          Meta-notation.md
[Notation]:               Notation/index.md
[Examples]:               Examples/index.md
[Examples.LC]:            Examples/LC/index.md
[Examples.PCF]:           Examples/PCF/index.md
[Examples.Scm]:           Examples/Scm/index.md
[Properties]:             Properties/index.md
[Tests]:                  Tests/index.md
[Tests.LC]:               Tests/LC/index.md
[Tests.PCF]:              Tests/PCF/index.md
[Library]:                Library/index.md

[mfps2026-agda]:          https://github.com/pdmosses/mfps2026-agda/

[Standard Agda library]:  https://agda.github.io/agda-stdlib/v2.3/