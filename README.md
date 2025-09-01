## Compilation

```shell
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install coq-mathcomp-real-closed coq-mathcomp-algebra-tactics
$ eval `opam env`
$ make
```

We have checked the compilation with the following versions of OPAM packages:
* rocq-core                    9.0.0
* rocq-elpi                    3.0.0
* rocq-hierarchy-builder       1.10.0
* rocq-mathcomp-ssreflect      2.4.0
* rocq-mathcomp-algebra        2.4.0
* rocq-mathcomp-field          2.4.0
* coq-mathcomp-zify            1.5.0+2.0+8.16
* coq-mathcomp-algebra-tactics 1.2.6
* coq-mathcomp-real-closed     2.0.3


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
* qexamples_misc.v: experiments: swap_cnot, hadamardU, etc.
