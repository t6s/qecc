## Compilation

opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-real-closed
eval `opam env`
make

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
