# qecc
This is an attempt at formalizing quantum circuit an a bit of kindergarten quantum mechanics in Coq/mathcomp.

File contents
* lens.v: definition of lens, extract, merge, and lemmas
* dpower.v: definition of dpower, morphisms, focus, and lemmas
* unitary.v: definition of unitaryts and unitary_endo
* endo_monoid.v: non-commutative and commutative morphism composition monoids
  for use with big operators
* qexamples_common.v: definition of basic gates
* qexamples_shor.v: proof of Shor's 9-qubit code
* qexamples_ghz.v: proof of Greenberger-Horne-Zeilinger preparation
* qexamples_rev_circuit.v: proof of the reverse circuit (using swap gates)

Presentation materials:
* Formalizing quantum circuits with MathComp/Ssreflect, Takafumi Saikawa and Jacques Garrigue, TPP 2021. [Slides](http://www.math.nagoya-u.ac.jp/~garrigue/papers/tpp2021-tpower-slides.pdf).
* Idem, PPL 2022. [Poster](http://www.math.nagoya-u.ac.jp/~garrigue/papers/tpower-poster-ppl2022.pdf).
* Idem, PlanQC 2022. [Poster](https://www.math.nagoya-u.ac.jp/~garrigue/papers/poster-planqc22.pdf)

By [Takefumi Saikawa](https://github.com/t6s) and [Jacques Garrigue](https://github.com/garrigue).
