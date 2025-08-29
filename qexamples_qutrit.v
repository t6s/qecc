From mathcomp Require Import all_ssreflect all_algebra complex ring.
Require Export lens lens_tactics dpower unitary density endo_monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope complex_scope.

Axiom R : rcfType.
Definition C : comRingType := R[i].
Definition Co : lmodType C := C^o.
Definition I : finType := 'I_3.
Definition dI : I := 0.

Notation "¦ x1 , .. , xn ⟩" :=
  (dpbasis _ [tuple of x1 :: .. [:: xn] ..]) (at level 0).

Notation dpsquare n := (dpmatrix I C n n).
Notation endo n := (mor I C n n).
Notation "T '^^' n" := (dpower I n T).

Definition ω : C := (3.-root (-1))^2.

Definition hadamard_dpmatrix : dpsquare 1 :=
  (1 / Num.sqrt 3)%:C *:
    (ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦0⟩ ¦2⟩ +
     ket_bra ¦1⟩ ¦0⟩ + ket_bra ¦2⟩ ¦0⟩ +
     ω *: (ket_bra ¦1⟩ ¦1⟩ + ket_bra ¦2⟩ ¦2⟩) +
     ω^2 *: (ket_bra ¦1⟩ ¦2⟩ + ket_bra ¦2⟩ ¦1⟩)).

Definition hadamard : endo 1 := dpmor hadamard_dpmatrix.

Definition qnot12 : endo 1 :=
    dpmor [ffun vi => let i := tnth vi 0 in ¦-i⟩].

Definition cnot : endo 2 :=
    dpmor [ffun vi => let i := tnth vi 0 in
                      let j := tnth vi 1 in
                      ¦i, i + j ⟩].

Definition swap : endo 2 :=
    dpmor [ffun vi => let i := tnth vi 0 in
                      let j := tnth vi 1 in
                      ¦j, i ⟩].

Section enum3.
Definition enum3 : seq I := [:: 0; 1; 2].
Lemma uniq_enum3 : uniq enum3. Proof. by []. Qed.
Lemma mem_enum3 i : i \in enum3.
Proof. by rewrite !inE; case: i => -[|[|[]]]. Qed.
End enum3.

(* Enumeration lemmas *)
Notation enum_indices := (enum_indices enum3).
Definition mem_enum_indices := mem_enum_indices mem_enum3.
Definition eq_from_indicesP := eq_from_indicesP mem_enum3.
Definition uniq_enum_indices := uniq_enum_indices uniq_enum3 mem_enum3.
Definition sum_enum_indices := sum_enum_indices uniq_enum3 mem_enum3.

Lemma cnotE (i j : I) : cnot Co ¦i, j⟩ = ¦i, i + j⟩.
Proof.
by apply/ffunP => vi; rewrite !ffunE !dpmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0).
Qed.

Lemma swapE (i j : I) : swap Co ¦i, j⟩ = ¦j, i⟩.
Proof.
by apply/ffunP => vi; rewrite !ffunE !dpmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0).
Qed.

Lemma qnot12E (i : I) : qnot12 Co ¦i⟩ = ¦-i⟩.
Proof.
by apply/ffunP => vi; rewrite !ffunE !dpmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0).
Qed.

Lemma hadamard2 : hadamard \v hadamard =e qnot12.
Proof.
apply/lift_mor_eq => vi.
rewrite -dpmor_comp.
congr (dpmor _ C^o vi).
apply/eq_from_indicesP => {vi} /=.
do! (apply/andP; split => //); rewrite ffunE; apply/eqP/ffunP=>/=vi; rewrite ffunE.
Admitted.

Lemma swap_cnot_qnot :
  swap =e cnot \v cnot \v focus [lens 1; 0] cnot \v focus [lens 0] qnot12 \v cnot.
Proof.
apply/eq_mor_basis => -[[|i [|j []]] Ht] //.
rewrite /= swapE cnotE focus_dpbasis.
simpl_extract.
rewrite qnot12E dpmerge_dpbasis.
simpl_merge dI.
rewrite focus_dpbasis.
simpl_extract.
rewrite cnotE dpmerge_dpbasis.
simpl_merge dI.
rewrite 2!cnotE addrAC subrr add0r.
have -> : j + (j + (i + j)) = 3 * j + i by ring.
by rewrite (@char_Zp 3) // !linE.
Qed.
