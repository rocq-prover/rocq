The Coq documentation
=====================

The Coq documentation includes

- A Reference Manual
- A document presenting the Coq standard library

The documentation of the latest released version is available on the Coq
web site at [rocq-prover.org/docs](https://rocq-prover.org/docs).

Additionally, you can view the reference manual for the development version
at <https://rocq-prover.org/doc/master/refman/>, and the documentation of the
standard library for the development version at
<https://rocq-prover.org/doc/master/stdlib/>.

The reference manual is written in reStructuredText and compiled
using Sphinx. See [`sphinx/README.rst`](sphinx/README.rst)
to learn more about the format that is used.

The documentation for the standard library is generated from
the `.v` source files using `rocq doc`.

Dependencies
------------

### HTML documentation

To produce the complete documentation in HTML, you will need Coq dependencies
listed in [`INSTALL.md`](../INSTALL.md). Additionally, the Sphinx-based
reference manual requires Python 3, and the following Python packages:

  - sphinx >= 5.0.0
  - sphinx_rtd_theme >= 1.1.0
  - beautifulsoup4 >= 4.10.0
  - antlr4-python3-runtime >= 4.7.1 & <= 4.9.3
  - pexpect >= 4.8.0
  - sphinxcontrib-bibtex >= 2.4.2

To install them, you should first install pip and setuptools (for instance,
with `apt install python3-pip python3-setuptools` on Debian / Ubuntu) then run:

    pip3 install sphinx sphinx_rtd_theme beautifulsoup4 \
                 antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex

Nix users should get the correct development environment to build the
HTML documentation from Coq's [`default.nix`](../default.nix) (note this
doesn't include the LaTeX packages needed to build the full documentation).

You can check the dependencies using the `doc/tools/coqrst/checkdeps.py` script.

### Other formats

To produce the documentation in PDF and PostScript formats, the following
additional tools are required:

  - latex (latex2e)
  - pdflatex
  - dvips
  - makeindex
  - xelatex
  - latexmk

All of them are part of the TexLive distribution. E.g. on Debian / Ubuntu,
install them with:

    apt install texlive-full

Or if you want to use less disk space:

    apt install texlive-latex-extra texlive-fonts-recommended texlive-xetex \
                latexmk fonts-freefont-otf

### JSON indices

The documentation generator can also produce computer-readable JSON files for individual indices
with `make refman-indices`. These files are meant to be useful for tool developers, for instance
to power autocompletion in editors. They output files are found in `doc/refman-indices/*.json`.

Each JSON index has the following shape:

```typescript
{
  // a key is the name of the index entry
  [string]: {
    // the refman documentation page path for that entry
    "documentation_path": string.
    // the anchor on that page that leads to the documentation entry
    "documentation_anchor": string,
    // the grammar description
    "syntax": Syntax,
    // a simpler, plain text documentation
    "documentation": string,
  }
}
```

Where `Syntax` can be used to match some text against the index entry or to propose the
user a code snippet. It is of the following shape:

```ts
type Syntax =
  | Literal
  | Reference
  | Alternative
  | Repeat

// the literal string
type Literal = {
  type: "literal"
  value: string
  // an optional subscript, for example "1" which should be rendered as "₁"
  subscript: string | null
}

// a reference to a different entry in the documentation
type Reference = {
  type: "reference"
  value: string
  // an optional subscript, for example "1" which should be rendered as "₁"
  subscript: string | null
}

// an alternative between a list of options
type Alternative = {
  type: "alternative"
  children: Syntax[]
}

// repetition of a list of syntax nodes
type Repeat = {
  type: "repeat"
  // nodes have to repeat at least this many times
  min: number
  // nodes can repeat up to and including this many times
  max: number | null
  // each repetition has to be separated with this
  separator: string | null
  children: Syntax[]
}
```

### Setting the locale for Python

Make sure that the locale is configured on your platform so that Python encodes
printed messages with utf-8 rather than generating runtime exceptions
for non-ascii characters.  The `.UTF-8` in `export LANG=C.UTF-8` sets UTF-8 encoding.
The `C` can be replaced with any supported language code.  You can set the default
for a Docker build with `ENV LANG C.UTF-8`.  (Python may look at other
environment variables to determine the locale; see the
[Python documentation](https://docs.python.org/3/library/locale.html#locale.getdefaultlocale)).

### Libraries

Most of the refman compiles with only the rocq-core package.
However, in order to showcase some nice advertising
examples with some external libraries included in Coq CI, a few code
blocks in the refman depend on those libraries. These blocks are
marked with the `extra` parameter (see
[`sphinx/README.rst`](sphinx/README.rst) for more details). The
targets below make those blocks optional but their correct compilation
is checked in the CI target `doc:ci-refman`.

Compilation
-----------

The current documentation targets are:

- `make refman-html`
  Build the reference manual in HTML form into `_build/default/doc/refman-html`

- `make refman-pdf`
  Build the reference manual in PDF form into `_build/default/doc/refman-pdf`

- `make corelib-html`
  Build Rocq core library documentation into `_build/default/doc/corelib/html`

- `make refman-indices`
  Build the JSON indices into `doc/refman-indices`

- `make apidoc`
  Build the ML API's documentation into `_build/default/_doc/_html`

To build the Sphinx documentation without stopping at the first
warning, change the value of the `SPHINXWARNOPT` variable (default is
`-W`). The following will build the Sphinx documentation without
stopping at the first warning, and store all the warnings in the file
`/tmp/warn.log`:

```
SPHINXWARNOPT="-w/tmp/warn.log" make refman-html
```

Note that inspecting local copies of the docs may behave in unexpected ways if
opening the sources with a browser (eg with `firefox
_build/default/doc/refman-html/index.html`). In order to avoid this, either
inspect the version generated by the CI or run a local server, for example
with:
```
cd _build/default/doc/refman-html/ && python3 -m http.server
```

Installation
------------

The produced documents are stored in the described directories above,
you can install them just by copying the contents to the desired
directory.

In the future, the `rocq-doc` and `rocq-core` opam packages will
install the documentation automatically.
