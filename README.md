## Compilation

$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install coq-mathcomp-real-closed coq-mathcomp-algebra-tactics
$ eval `opam env`
$ make

We have checked the compilation with the following versions of OPAM packages:
coq                          8.19.0
coq-core                     8.19.0
coq-elpi                     2.0.2
coq-hierarchy-builder        1.7.0
coq-mathcomp-algebra         2.2.0
coq-mathcomp-algebra-tactics 1.2.3
coq-mathcomp-bigenough       1.0.1
coq-mathcomp-field           2.2.0
coq-mathcomp-fingroup        2.2.0
coq-mathcomp-real-closed     2.0.0
coq-mathcomp-solvable        2.2.0
coq-mathcomp-ssreflect       2.2.0
coq-mathcomp-zify            1.5.0+2.0+8.16
coq-stdlib                   8.19.0

## File contents

* mathcomp_extra.v: additions to mathcomp library
* lens.v: definition of lens, extract, merge, and lemmas
* dpower.v: definition of dpower, morphisms, focus, and lemmas
* unitary.v: definition of unitaryts and unitary_endo
* endo_monoid.v: non-commutative and commutative morphism composition monoids
  for use with big operators
* density.v: definition of the density matrix interpretation
* kqm.v: some experiments with caps and cups
* qexamples_common.v: definition of basic gates
* qexamples_shor.v: proof of Shor's 9-qubit code
* qexamples_ghz.v: proof of Greenberger-Horne-Zeilinger preparation
* qexamples_rev_circuit.v: proof of the reverse circuit (using swap gates)
* qexamples_qutrit.v: examples with qutrit gates, including CNOT and SWAP
