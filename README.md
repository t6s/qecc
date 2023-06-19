## Compilation

$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install coq-mathcomp-real-closed
$ eval `opam env`
$ make

We have checked the compilation with the following versions of packages:

ocaml-options-vanilla    1
ocaml-base-compiler      5.0.0  [required by ocaml]
conf-gmp                 4      [required by zarith]
base-bigarray            base
base-threads             base   [required by dune]
base-unix                base   [required by dune]
ocaml-config             3      [required by ocaml]
ocaml                    5.0.0  [required by coq-core]
ocamlfind                1.9.6  [required by coq-core]
dune                     3.7.1  [required by coq]
base-domains             base
zarith                   1.12   [required by coq-core]
base-nnp                 base
coq-core                 8.17.0 [required by coq]
coqide-server            8.17.0 [required by coq]
coq-stdlib               8.17.0 [required by coq]
coq                      8.17.0 [required by coq-mathcomp-real-closed]
coq-mathcomp-ssreflect   1.17.0 [required by coq-mathcomp-real-closed]
coq-mathcomp-fingroup    1.17.0 [required by coq-mathcomp-algebra]
coq-mathcomp-bigenough   1.0.1  [required by coq-mathcomp-real-closed]
coq-mathcomp-algebra     1.17.0 [required by coq-mathcomp-real-closed]
coq-mathcomp-solvable    1.17.0 [required by coq-mathcomp-field]
coq-mathcomp-field       1.17.0 [required by coq-mathcomp-real-closed]
coq-mathcomp-real-closed 1.1.4


## File contents

* lens.v: definition of lens, extract, merge, and lemmas
* dpower.v: definition of dpower, morphisms, focus, and lemmas
* unitary.v: definition of unitaryts and unitary_endo
* endo_monoid.v: non-commutative and commutative morphism composition monoids
  for use with big operators
* qexamples_common.v: definition of basic gates
* qexamples_shor.v: proof of Shor's 9-qubit code
* qexamples_ghz.v: proof of Greenberger-Horne-Zeilinger preparation
* qexamples_rev_circuit.v: proof of the reverse circuit (using swap gates)
