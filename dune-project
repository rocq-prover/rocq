(lang dune 3.8)
(name rocq-prover)

; We use directory targets in documentation
(using directory-targets 0.1)

; We need this for when we use the dune.disabled files instead of our rule_gen
(using coq 0.8)

(formatting
 (enabled_for ocaml))

(generate_opam_files true)

(license LGPL-2.1-only)
(maintainers "The Rocq development team <coqdev@inria.fr>")
(authors "The Rocq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github rocq-prover/rocq))
(homepage https://rocq-prover.org/)
(documentation "https://rocq-prover.org/docs/")
(version dev)

; Note that we use rocq-runtime.opam.template to have dune add the correct opam
; prefix for configure
(package
 (name rocq-runtime)
 (depends
  (ocaml (>= 4.09.0))
  (ocamlfind (>= 1.8.1))
  (zarith (>= 1.11))
  (conf-linux-libc-dev (= :os "linux")))
 (conflicts
  (coq (< 8.17))
  (coq-core (< 8.21)))
 (depopts rocq-native memprof-limits memtrace)
 (synopsis "The Rocq Prover -- Core Binaries and Tools")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq Prover core binaries, plugins, and tools, but
not the vernacular standard library.

Note that in this setup, Rocq needs to be started with the -boot and
-noinit options, as will otherwise fail to find the regular Rocq
prelude, now living in the rocq-core package."))

(package
 (name rocq-devtools)
 (depends
  (rocq-runtime (= :version))
   yojson
   camlzip)
 (synopsis "Development tools for Rocq")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes tools to help when developing Rocq projects
(timelog2html)."))

(package
 (name coq-core)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "Compatibility binaries for Coq after the Rocq renaming")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes compatibility binaries to call Rocq
through previous Coq commands like coqc coqtop,..."))

(package
 (name rocq-core)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "The Rocq Prover with its prelude")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq prelude, that is loaded automatically
by Rocq in every .v file, as well as other modules bound to the
Corelib.* and Ltac2.* namespaces."))

(package
 (name coqide-server)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "The Rocq Prover, XML protocol server")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the `coqidetop` language server, an
implementation of Rocq's [XML protocol](https://github.com/rocq-prover/rocq/blob/master/dev/doc/xml-protocol.md)
which allows clients, such as RocqIDE, to interact with the Rocq Prover in a
structured way."))

(package
 (name rocqide)
 (depends
  (ocamlfind :build)
  (conf-findutils :build)
  conf-adwaita-icon-theme
  (coqide-server (= :version))
  (cairo2 (>= 0.6.4))
  (lablgtk3-sourceview3 (and (>= 3.1.2) (or (>= 3.1.5) (<> :os "windows")))))
 (synopsis "The Rocq Prover --- GTK3 IDE")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the RocqIDE, a graphical user interface for the
development of interactive proofs."))

(package
 (name rocq-doc)
 (license "OPUBL-1.0")
 (depends
  (conf-python-3 :build)
  (coq (and :build (= :version))))
 (synopsis "The Rocq Prover --- Reference Manual")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the Rocq Reference Manual."))

(package
 (name rocq-test-suite)
 (depends
  (rocq-core (= :version))
  coqide-server
  ounit2
  conf-python-3
  conf-time)
 (synopsis "The Rocq Prover test suite")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package runs the test suite."))

(package
 (name rocq-native)
 (conflicts base-nnp ocaml-option-nnpchecker)
 (synopsis "Package flag enabling rocq's native-compiler flag")
 (description "This package acts as a package flag for the ambient switch, taken into
account by rocq (and possibly any rocq library) to enable native_compute
at configure time, triggering the installation of .coq-native/* files
for the rocq libraries.

This implements item 1 of CEP #48 <https://github.com/coq/ceps/pull/48>.

Remarks:

1. you might face with issues installing this package flag under macOS,
   see <https://github.com/coq/coq/issues/11178>.
2. this package is not intended to be used as a dependency of other
   packages (notably as installing or uninstalling this package may
   trigger a rebuild of all rocq packages in the ambient switch).
3. the option set by this package will be automatically propagated to
   rocq compile."))

(package
 (name coq-native)
 (conflicts (coq (< 8.5)))
 (synopsis "Package flag enabling coq's native-compiler flag")
 (description "This package acts as a package flag for the ambient switch, taken into
account by coq (and possibly any coq library) to enable native_compute
at configure time, triggering the installation of .coq-native/* files
for the coq standard library and subsequent coq libraries.

This implements item 1 of CEP #48 <https://github.com/coq/ceps/pull/48>.

Remarks:

1. you might face with issues installing this package flag under macOS,
   see <https://github.com/coq/coq/issues/11178>.
2. this package is not intended to be used as a dependency of other
   packages (notably as installing or uninstalling this package may
   trigger a rebuild of all coq packages in the ambient switch).
3. the option set by this package will be automatically propagated to
   coqc for coq >= 8.13 (but the packaging of coq libraries for
   earlier versions of coq may need an update: for details, see item 3
   of CEP #48 <https://github.com/coq/ceps/pull/48>).
"))
