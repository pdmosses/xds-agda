# Denotational Semantics in Agda

> Experiments with Agda support for Scott–Strachey denotational semantics

## About

For background and motivation, see the generated [website].

## Examples

- [Lambda-calculus]
- [PCF]
- [Scm]

## Website

This repository illustrates the use of **[Agda-Pages]** to
**generate websites** with **module navigation** between
**highlighted, hyperlinked listings** of Agda code.

See the **[Agda-Pages About]** page for an overview of the features
of the generated website, and for links to further examples.

The **[Agda-Pages User Guide]** explains how to generate a website listing
Agda code in any GitHub repository.

See the **[Agda-Pages README]** for how to install Agda-Pages,
and for a list of its main software dependencies.

The following shell commands generated the XDS-Agda website from this branch
of the repository, then previewed it locally:

```shell
cd pages
make check
make web
make serve
```

Version `...` of the generated website is deployed on GitHub Pages by:

```shell
make deploy VERSION=...
```

## Contributing

Please report any [issues] that arise.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

[website]:               https://pdmosses.github.io/xds-agda/dev/
[Lambda-calculus]:       https://pdmosses.github.io/xds-agda/dev/LC/
[PCF]:                   https://pdmosses.github.io/xds-agda/dev/PCF/
[Scm]:                   https://pdmosses.github.io/xds-agda/dev/Scm/

[Agda-Pages]:            https://pdmosses.github.io/agda-pages/
[Agda-Pages About]:      https://pdmosses.github.io/agda-pages/About/
[Agda-Pages User Guide]: https://pdmosses.github.io/agda-pages/User-Guide/
[Agda-Pages repository]: https://github.com/pdmosses/agda-pages/
[Agda-Pages README]:     https://github.com/pdmosses/agda-pages/blob/main/README.md

[Issues]:                https://github.com/pdmosses/xds-agda/issues
[Pull requests]:         https://github.com/pdmosses/xds-agda/pulls
[Discussions]:           https://github.com/pdmosses/xds-agda/discussions
