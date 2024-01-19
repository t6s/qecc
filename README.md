## Compilation

$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install coq-mathcomp-real-closed
$ eval `opam env`
$ make

We have checked the compilation with the following versions of OPAM packages:
base-bigarray            base
base-threads             base
base-unix                base
conf-findutils           1
conf-gmp                 4
coq                      8.17.1
coq-core                 8.17.1
coq-mathcomp-algebra     1.17.0
coq-mathcomp-bigenough   1.0.1
coq-mathcomp-field       1.17.0
coq-mathcomp-fingroup    1.17.0
coq-mathcomp-real-closed 1.1.4
coq-mathcomp-solvable    1.17.0
coq-mathcomp-ssreflect   1.17.0
coq-stdlib               8.17.1
coqide-server            8.17.1
dune                     3.10.0
ocaml                    4.12.2
ocaml-config             2
ocaml-variants           4.12.2+trunk
ocamlfind                1.9.6
zarith                   1.13


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
