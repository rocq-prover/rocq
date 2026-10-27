- **Added:**
  Universes as components of modules and module types: :cmd:`Universe Parameter`
  declares an abstract universe in a module type (or module), and
  :cmd:`Universe Definition` declares a universe of a module equal to an
  existing universe. Such universes are substituted along with the other
  components of the module through functor application, module aliasing and
  inclusion, so that module types can be parametric in universes, and a
  module type can be refined with
  :n:`with Universe Definition @qualid := @universe_name`
  (`#22646 <https://github.com/rocq-prover/rocq/pull/22646>`_,
  by Matthieu Sozeau).
