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
Notation mxapp l M := (focus l (mxmor M)).
Notation dpsquare n := (dpmatrix I C n n).
Notation endo n := (mor I C n n).
Notation "T '^^' n" := (dpower I n T).

Definition qnot : dpsquare 1 :=
  [ffun vi => let i := tnth vi 0 in ¦1+i⟩].

Definition cnot : dpsquare 2 :=
  [ffun vi => let i := tnth vi 0 in let j := tnth vi 1 in ¦i, i+j⟩].

Definition minus1 : C := -1.
Definition opp_ket_bra n (v1 v2 : Co ^^ n) := - ket_bra v1 v2.

Definition hadamard : dpsquare 1 :=
  (1 / Num.sqrt 2)%:C *:
    (-ket_bra ¦1⟩ ¦1⟩ + ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩).

Definition toffoli : dpsquare 3 :=
  [ffun vi =>
     let i := tnth vi 0 in let j := tnth vi 1 in let k := tnth vi 2 in
     ¦i,j,i*j+k⟩ ].
(* =
  ket_bra ¦0,0,0⟩ ¦0,0,0⟩ + ket_bra ¦0,0,1⟩ ¦0,0,1⟩ +
  ket_bra ¦0,1,0⟩ ¦0,1,0⟩ + ket_bra ¦0,1,1⟩ ¦0,1,1⟩ +
  ket_bra ¦1,0,0⟩ ¦1,0,0⟩ + ket_bra ¦1,0,1⟩ ¦1,0,1⟩ +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩. *)

Definition swap : dpsquare 2 :=
  [ffun vi => let i := tnth vi 0 in let j := tnth vi 1 in ¦j,i⟩ ].

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

Lemma mxmor_cnot (i j : I) : mxmor cnot Co ¦i, j⟩ = ¦i, i + j⟩.
Proof.
apply/ffunP => vi.
by rewrite !ffunE !mxmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0).
Qed.

Lemma mxmor_swap (i j : I) : mxmor swap Co ¦i, j⟩ = ¦j, i⟩.
Proof.
apply/ffunP => vi.
by rewrite !ffunE !mxmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0).
Qed.

Lemma addii (i : I) : i + i = 0.
Proof. by have:=mem_enum2 i; rewrite !inE => /orP[]/eqP->; apply/val_inj. Qed.

Lemma mxmor_toffoli00 i : mxmor toffoli Co ¦0,0,i⟩ = ¦0,0,i⟩.
Proof.
apply/ffunP => vi.
by rewrite !ffunE !mxmorE /= sum_dpbasisKo !ffunE !(tnth_nth 0) /= !linE.
Qed.

(* Unitarity *)

Lemma rev_inj A : injective (@rev A).
Proof.
elim => [|a l1 IH] [|b l2] //=.
- move/(f_equal size). by rewrite !size_rev.
- move/(f_equal size). by rewrite !size_rev.
- by rewrite !rev_cons => /rcons_inj [] /IH -> ->.
Qed.

Lemma swapS : dptranspose swap = swap.
Proof.
apply/ffunP=> vi; apply/ffunP=> vj.
rewrite !ffunE.
case: vi => [] [|i1 [|i2 []]] // Hi.
case: vj => [] [|j1 [|j2 []]] // Hj /=.
rewrite !eq_ord_tuple /= !(tnth_nth 0) /=.
by rewrite -(inj_eq (@rev_inj _) [::nat_of_ord j2;_]) eq_sym.
Qed.

Lemma swapU : unitary_mor (mxmor swap).
Proof.
rewrite /unitary_mor /tinner => s t.
under eq_bigr => vi _. rewrite !mxmorE.
  under eq_bigr do rewrite -swapS !ffunE.
  set u := [tuple _;_].
  rewrite (bigD1 u) //= eqxx /= scale1r big1; last first.
    by move=> i Hi; rewrite eq_sym (negbTE Hi) scale0r.
  rewrite addr0.
  under eq_bigr do rewrite -swapS !ffunE -/u.
  rewrite (bigD1 u) //= eqxx /= scale1r big1; last first.
    by move=> i Hi; rewrite eq_sym (negbTE Hi) scale0r.
  rewrite addr0 /u.
  over.
rewrite !sum_enum_indices /=.
rewrite !addrA !addr0 [X in X + _]addrAC.
do !congr GRing.add; by rewrite !{1}ffunE /= !linE !sum_dpbasisK.
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
rewrite !mxmorE !sum_enum_indices /= !linE /= !{1}ffunE /= !linE.
rewrite !mxmorE !sum_enum_indices /= !linE /= !{1}ffunE /= !linE.
rewrite ![_ *: 1]mulr1.
rewrite !scalerDr !scalerN ![_ *: 1]mulr1 !scalerA !(mulrN,mulNr); simpc.
simpc.
rewrite !linE -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //=.
rewrite !addrA [X in X + _]addrAC opprK -scalerDl -addrA -scalerDl.
rewrite (addrAC (_ *: _)) -scalerDl -addrA -scalerDl.
simpc.
by rewrite subrr !linE -mulr2n -(mulr_natl (_^-1)) Hnn !scale1r !eqxx.
Qed.
