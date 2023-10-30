From mathcomp Require Import all_ssreflect all_algebra complex.
Require Export lens dpower unitary endo_monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope complex_scope.

Axiom R : rcfType.
Definition C := [comRingType of R[i]].
Definition Co := [lmodType C of C^o].
Definition I := [finType of 'I_2].
Definition dI : I := 0.

Notation "¦ x1 , .. , xn ⟩" :=
  (dpbasis _ [tuple of x1 :: .. [:: xn] ..]) (at level 0).

Notation focus := (focus dI).
Notation mxapp l M := (focus l (mxmor M)).
Notation dpsquare n := (dpmatrix I C n n).
Notation endo n := (mor I C n n).
Notation "T '^^' n" := (dpower I n T).

Definition qnot : dpsquare 1 :=
  ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩.

Definition cnot : dpsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦0,1⟩ +
  ket_bra ¦1,0⟩ ¦1,1⟩ + ket_bra ¦1,1⟩ ¦1,0⟩.

Definition hadamard : dpsquare 1 :=
  (1 / Num.sqrt 2)%:C *:
    (ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩ - ket_bra ¦1⟩ ¦1⟩).

Definition toffoli : dpsquare 3 :=
  (\sum_(k <- [:: ¦0,0,0⟩; ¦0,0,1⟩; ¦0,1,0⟩; ¦0,1,1⟩; ¦1,0,0⟩; ¦1,0,1⟩])
      ket_bra k k) +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩.
(* =
  ket_bra ¦0,0,0⟩ ¦0,0,0⟩ + ket_bra ¦0,0,1⟩ ¦0,0,1⟩ +
  ket_bra ¦0,1,0⟩ ¦0,1,0⟩ + ket_bra ¦0,1,1⟩ ¦0,1,1⟩ +
  ket_bra ¦1,0,0⟩ ¦1,0,0⟩ + ket_bra ¦1,0,1⟩ ¦1,0,1⟩ +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩. *)

Definition swap : dpsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,0⟩ +
  ket_bra ¦1,0⟩ ¦0,1⟩ + ket_bra ¦1,1⟩ ¦1,1⟩.

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

Lemma mxmor_cnot0 i : mxmor cnot Co ¦0,i⟩ = ¦0,i⟩.
Proof.
apply/ffunP => vi; rewrite !ffunE mxmorE sum_dpbasisKo !ffunE !eq_ord_tuple /=.
have := mem_enum2 i; rewrite !inE => /orP[] /eqP -> /=;
by rewrite !scaler0 !linE [LHS]mulr1.
Qed.

Definition flip (i : I) := rev_ord i.
Lemma mxmor_cnot1 i : mxmor cnot Co ¦1, i⟩ = ¦1, flip i⟩.
Proof.
apply/ffunP => vi; rewrite !ffunE mxmorE sum_dpbasisKo !ffunE !eq_ord_tuple /=.
have := mem_enum2 i; rewrite !inE => /orP[] /eqP -> /=;
by rewrite !scaler0 !linE [LHS]mulr1.
Qed.

Lemma flip_addr i : flip i = 1 + i.
Proof. by have:=mem_enum2 i; rewrite !inE => /orP[]/eqP-> ; apply/val_inj. Qed.

Lemma mxmor_cnot (i j : I) : mxmor cnot Co ¦i, j⟩ = ¦i, i + j⟩.
Proof.
have := mem_enum2 i; rewrite !inE => /orP[] /eqP -> /=.
- by rewrite mxmor_cnot0 add0r.
- by rewrite mxmor_cnot1 flip_addr.
Qed.

Lemma mxmor_swap (i j : I) : mxmor swap Co ¦i, j⟩ = ¦j, i⟩.
Proof.
have := mem_enum2 i; rewrite !inE => /orP[] /eqP ->;
have := mem_enum2 j; rewrite !inE => /orP[] /eqP -> /=;
apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time (by rewrite !(mxmorE,linE,sum_dpbasisK,ffunE)).
Qed.

Lemma addii (i : I) : i + i = 0.
Proof. by have:=mem_enum2 i; rewrite !inE => /orP[]/eqP->; apply/val_inj. Qed.

Lemma mxmor_toffoli00 i : mxmor toffoli Co ¦0,0,i⟩ = ¦0,0,i⟩.
Proof.
apply/ffunP => vi.
rewrite !ffunE mxmorE sum_dpbasisKo !ffunE !eq_ord_tuple /= !scaler0 !addr0.
rewrite BigOp.bigopE /= !ffunE !eq_ord_tuple /= !scaler0 !addr0.
have := mem_enum2 i; rewrite !inE => /orP[] /eqP -> /=;
by rewrite !scaler0 !linE [LHS]mulr1.
Qed.

(* Unitarity *)

Lemma swapU : unitary_endo (mxmor swap).
Proof.
rewrite /unitary_endo /tinner /= => s t.
rewrite !sum_enum_indices /= !mxmorE.
time (rewrite !ffunE /= !linE).
rewrite !sum_dpbasisK.
by rewrite !addrA -(addrA (_ * _)) (addrC (_ * _) (_ * _)) !addrA.
Qed.

(* Hadamard gate is involutive *)
Lemma sqrt_nat_unit n : (Num.sqrt n.+1%:R : R) \is a GRing.unit.
Proof. by rewrite unitf_gt0 // -sqrtr0 ltr_sqrt ltr0Sn. Qed.

Lemma nat_unit n : (n.+1%:R : R)%R \is a GRing.unit.
Proof. by rewrite unitf_gt0 // ltr0Sn. Qed.

Lemma hadamardK T : involutive (mxmor hadamard T).
Proof.
have Hnn n : n.+1%:R / n.+1%:R = 1 :>R by rewrite divrr // nat_unit.
move=> v; apply/eq_from_indicesP => //=.
time (do! rewrite !(linE,ffunE,mxmorE,scalerDl,sum_enum_indices) /=).
rewrite -mulNrn !mulr1n -!scalerA.
rewrite !scale1r !scalerDr !scaleN1r !scalerN !scalerA.
simpc.
rewrite !linE -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //.
do! (apply/andP; split) => //=.
1: rewrite addrCA -addrA subrr linE -scalerDl.
2: rewrite opprK addrAC !addrA subrr linE -scalerDl.
all: rewrite -mulr2n -mulr_natl -rmorphMn /=; simpc.
all: by rewrite Hnn mul0r scale1r.
Qed.

