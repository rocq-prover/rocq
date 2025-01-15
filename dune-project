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
(maintainers "The Rocq development team <rocq+rocq-development@discoursemail.com>")
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
  (ocaml (>= 4.14.0))
  (ocamlfind (and (>= 1.9.1) (or (>= 1.9.8) (<> :os "windows"))))
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
  (yojson (>= 2.0))
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
