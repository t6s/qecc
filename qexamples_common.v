From mathcomp Require Import all_ssreflect all_algebra complex.
Require Export lens dpower unitary endo_monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope complex_scope.

Axiom R : rcfType.
Definition C : comRingType := R[i].
Definition Co : lmodType C := C^o.
Definition I : finType := 'I_2.
Definition dI : I := 0.

Notation "¦ x1 , .. , xn ⟩" :=
  (dpbasis _ [tuple of x1 :: .. [:: xn] ..]) (at level 0).

Notation focus := (focus dI).
Notation dpapp l M := (focus l (dpmor M)).
Notation dpsquare n := (dpmatrix I C n n).
Notation endo n := (mor I C n n).
Notation "T '^^' n" := (dpower I n T).
Notation "t '!_' i" := (tnth t i) (at level 9).

Definition qnot : endo 1 :=
  dpmor [ffun vi => ¦1 + vi!_0⟩].

Definition cnot : endo 2 :=
  dpmor [ffun vi => let i := vi!_0 in let j := vi!_1 in ¦i, i+j⟩].

Definition hadamard_dpmatrix : dpsquare 1 :=
  (1 / Num.sqrt 2)%:C *:
    (-ket_bra ¦1⟩ ¦1⟩ + ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩).

Definition hadamard : endo 1 := dpmor hadamard_dpmatrix.

Definition toffoli : endo 3 :=
  dpmor [ffun vi =>
           let i := vi!_0 in let j := vi!_1 in let k := vi!_2 in ¦i,j,i*j+k⟩ ].
(* =
  ket_bra ¦0,0,0⟩ ¦0,0,0⟩ + ket_bra ¦0,0,1⟩ ¦0,0,1⟩ +
  ket_bra ¦0,1,0⟩ ¦0,1,0⟩ + ket_bra ¦0,1,1⟩ ¦0,1,1⟩ +
  ket_bra ¦1,0,0⟩ ¦1,0,0⟩ + ket_bra ¦1,0,1⟩ ¦1,0,1⟩ +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩. *)

Definition swap_dpmatrix : dpsquare 2 := [ffun vi => ¦ vi!_1, vi!_0 ⟩ ].
Definition swap : endo 2 := dpmor swap_dpmatrix.

(* Enumeration lemmas *)
Notation enum_indices := (enum_indices enum2).
Definition mem_enum_indices := mem_enum_indices mem_enum2.
Definition eq_from_indicesP := eq_from_indicesP mem_enum2.
Definition uniq_enum_indices := uniq_enum_indices uniq_enum2 mem_enum2.
Definition sum_enum_indices := sum_enum_indices uniq_enum2 mem_enum2.
Definition dpmerge_dpbasis := dpmerge_dpbasis (0 : I).

(* A bit of automation to avoid stalling on dependent types *)

Ltac succOE H n :=
  match n with 0%N => rewrite ?succO0 in H
  | S ?m => succOE H m; rewrite ?(@succOS _ m.+1) in H
  end.

Ltac simpl_lens x :=
  let y := fresh "y" in
  pose y := val (val x);
  rewrite /= ?(tnth_nth 0) /= in y; unfold seq_lensC in y;
  rewrite /= ?enum_ordinalE /= ?(tnth_nth 0) /= in y; succOE y 10%N;
  rewrite (_ : x = @mkLens _ _ [tuple of y] erefl); first subst y;
  last by eq_lens; rewrite /= ?enum_ordinalE.

Ltac simpl_lens_comp :=
  match goal with
  |- context [ lens_comp ?a ?b ] => simpl_lens (lens_comp a b)
  end.

Goal lensC ([lens 0; 1] : lens 4 _) = [lens 2; 3].
set x := lensC _.
simpl_lens x.
Abort.

Ltac simpl_tuple x :=
  let y := fresh "y" in
  pose y := val x;
  rewrite /= ?(tnth_nth 0) /= in y; unfold seq_lensC in y;
  rewrite /= ?enum_ordinalE /= ?(tnth_nth 0) /= in y;
  rewrite (_ : x = [tuple of y]); last (by eq_lens); subst y.

Ltac simpl_extract :=
  match goal with |- context [ extract ?a ?b ] => simpl_tuple (extract a b)
  end.

Ltac simpl_merge :=
  match goal with |- context [ merge ?a ?b ?c ?d] => simpl_tuple (merge a b c d)
  end.

(* Behavior of some gates on basis vectors *)

Lemma qnotE (i : I) : qnot Co ¦i⟩ = ¦1 + i⟩.
Proof. by rewrite dpmor_dpbasis ffunE. Qed.

Lemma cnotE (i j : I) : cnot Co ¦i, j⟩ = ¦i, i + j⟩.
Proof. by rewrite dpmor_dpbasis ffunE. Qed.

Lemma swapE (i j : I) : swap Co ¦i, j⟩ = ¦j, i⟩.
Proof. by rewrite dpmor_dpbasis ffunE. Qed.

Lemma addii (i : I) : i + i = 0.
Proof. by rewrite -mulr2n -mulr_natl (@char_Zp 2) // mul0r. Qed.

Lemma toffoliE i j k : toffoli Co ¦i,j,k⟩ = ¦i,j,i*j+k⟩.
Proof. by rewrite dpmor_dpbasis ffunE. Qed.

Lemma toffoli00E i : toffoli Co ¦0,0,i⟩ = ¦0,0,i⟩.
Proof. by rewrite toffoliE !linE. Qed.

(* Unitarity *)

Lemma rev_inj A : injective (@rev A).
Proof.
elim => [|a l1 IH] [|b l2] //=.
- move/(f_equal size). by rewrite !size_rev.
- move/(f_equal size). by rewrite !size_rev.
- by rewrite !rev_cons => /rcons_inj [] /IH -> ->.
Qed.

Lemma swapS : dptranspose swap_dpmatrix = swap_dpmatrix.
Proof.
apply/eq_from_indicesP; do! (apply/andP; split => //);
  apply/eqP/eq_from_indicesP; by rewrite /= !ffunE !(tnth_nth 0) /= !eqxx.
Qed.

Lemma swapU : unitary_mor swap.
Proof.
apply/(unitary_morP dI)/eqP.
apply/eq_from_indicesP; do! (apply/andP; split => //);
  apply/eqP/eq_from_indicesP; do! (apply/andP; split => //=).
all: by rewrite !ffunE /= !sum_dpbasisKo !ffunE conjc_nat !(tnth_nth 0).
Qed.

(* Hadamard gate is involutive *)
Lemma sqrt_nat_unit n : (Num.sqrt n.+1%:R : R) \is a GRing.unit.
Proof. by rewrite unitf_gt0 // -sqrtr0 ltr_sqrt ltr0Sn. Qed.

Lemma nat_unit n : (n.+1%:R : R)%R \is a GRing.unit.
Proof. by rewrite unitf_gt0 // ltr0Sn. Qed.

Lemma hadamardK T : involutive (hadamard T).
Proof.
have Hnn n : n.+1%:R / n.+1%:R = 1 :>R by rewrite divrr // nat_unit.
move=> v; apply/eq_from_indicesP => //=.
rewrite !dpmorE !sum_enum_indices /= !linE /= !{1}ffunE /= !linE.
rewrite !dpmorE !sum_enum_indices /= !linE /= !{1}ffunE /= !linE.
rewrite ![_ *: 1]mulr1.
rewrite !scalerDr !scalerN ![_ *: 1]mulr1 !scalerA !(mulrN,mulNr); simpc.
rewrite !linE -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //=.
rewrite !addrA [X in X + _]addrAC opprK -scalerDl -addrA -scalerDl.
rewrite (addrAC (_ *: _)) -scalerDl -addrA -scalerDl.
simpc.
by rewrite subrr !linE -mulr2n -(mulr_natl (_^-1)) Hnn !scale1r !eqxx.
Qed.
