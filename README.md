# Denotational Semantics in Agda

> Experiments with Agda support for Scott–Strachey denotational semantics

The `Makefile` in this repository has the following targets:

- `check`: check the Agda code;
- `website`: generate a website for browsing the code;
- `serve`: preview the website locally;
- `deploy`: deploy the website to GitHub Pages; and
- `help`: list all targets.

The generated website is deployed at https://pdmosses.github.io/xds-agda/.

## About

For background and motivation, see the generated [website].

## Examples

- [Lambda-calculus]
- [PCF]
- [Scm]

## Repository contents

The [repository] contains the following files and directories:

- `agda`: directory for Agda source code of the ScmQE language
- `docs`: directory for generating a website
    - `docs/javascripts`: directory for added Javascript files
    - `docs/stylesheets`: directory for added CSS files
    - `docs/.nav.yml`: configuration file for navigation panels
    - `docs/*.md`: Markdown sources for non-generated pages
- `agda-custom.sty`: package for overriding commands defined in `agda.sty`
- `agda-unicode.sty`: package mapping Unicode characters to LaTeX
- `UNLICENSE`: release into the public domain
- `Makefile`: automation of website and PDF generation
- `mkdocs.yml`: configuration file for generated websites

The repository does not contain any generated files.

## Software dependencies

- [Agda] (2.7.0)
- [GNU Make] (3.8.1)
- [sd] (1.0.0)

### For website generation

- [Python 3] (3.11.3)
- [Pip] (25.2)
- [MkDocs] (1.6.1)
- [Material for MkDocs] (9.6.19)
- [Awesome-nav] (3.2.0)
- [GitHub Pages]

### For PDF generation

- [TeXLive] (2025)

## Platform dependencies

Agda-Material has been developed and tested on MacBook laptops
with Apple M1 and M3 chips running macOS Sequoia (15.5) with CLI Tools.

Please report any [issues] with using Agda-Material on other platforms,
including all relevant details.

[Pull requests] for addressing such issues are welcome. They should include the
results of tests that demonstrate the benefit of the PR.

## Getting started

All `make` commands are to be run in the repository root directory.

### Test the Agda code

```sh
make check
```

### Generate a website listing the Agda code

```sh
make website
```

### Browse the website locally

```sh
make serve
```

### Deploy the website on GitHub Pages

Update the following fields in `mkdocs.yml`:

- `site_name`
- `site_url`
- `repo_name`
- `repo_url`

```sh
make deploy
```

## Contributing

Please report any [issues] that arise.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

## Discussion

Advice and suggestions are welcome, e.g., by posting to the repo [Discussions].

Peter Mosses <p.d.mosses@tudelft.nl>

[repository]: https://github.com/pdmosses/xds-agda/
[website]: https://pdmosses.github.io/xds-agda/
[Lambda-calculus]: https://pdmosses.github.io/xds-agda/LC/
[PCF]: https://pdmosses.github.io/xds-agda/PCF/
[Scm]: https://pdmosses.github.io/xds-agda/Scm/

[Issues]: https://github.com/pdmosses/xds-agda/issues
[Pull requests]: https://github.com/pdmosses/xds-agda/pulls
[Discussions]: https://github.com/pdmosses/xds-agda/discussions

[Home page]: index.md
[Agda]: https://agda.readthedocs.io/en/stable/getting-started/index.html
[GNU Make]: https://www.gnu.org/software/make/manual/make.html
[sd]: https://github.com/chmln/sd/
[Python 3]: https://www.python.org/downloads/
[Pip]: https://pypi.org/project/pip/
[MkDocs]: https://www.mkdocs.org/getting-started/
[Material for MkDocs]: https://squidfunk.github.io/mkdocs-material/getting-started/
[Awesome-nav]: https://lukasgeiter.github.io/mkdocs-awesome-nav/
[GitHub Pages]: https://pages.github.com
[TeXLive]: https://www.tug.org/texlive/