From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section shor_code.

Definition bit_flip_enc : endo 3 :=
  focus [lens 0; 2] cnot \v  focus [lens 0; 1] cnot.

Definition bit_flip_dec : endo 3 :=
  focus [lens 1; 2; 0] toffoli \v bit_flip_enc.

Definition bit_flip_code (chan : endo 3) : endo 3 :=
  bit_flip_dec \v chan \v bit_flip_enc.

Definition hadamard3 : endo 3 :=
  focus [lens 2] hadamard \v focus [lens 1] hadamard \v focus [lens 0] hadamard.

Definition sign_flip_dec := bit_flip_dec \v hadamard3.
Definition sign_flip_enc := hadamard3 \v bit_flip_enc.

Definition sign_flip_code (chan : endo 3) :=
  sign_flip_dec \v chan \v sign_flip_enc.

Definition shor_enc : endo 9 :=
  focus [lens 0; 1; 2] bit_flip_enc \v focus [lens 3; 4; 5] bit_flip_enc \v
  focus [lens 6; 7; 8] bit_flip_enc \v focus [lens 0; 3; 6] sign_flip_enc.

Definition shor_dec : endo 9 :=
  focus [lens 0; 3; 6] sign_flip_dec \v focus [lens 0; 1; 2] bit_flip_dec \v
  focus [lens 3; 4; 5] bit_flip_dec \v focus [lens 6; 7; 8] bit_flip_dec.

Definition shor_code (chan : endo 9) :=
  shor_dec \v chan \v shor_enc.

(* Proof of correctness for Shor code *)

(* bit flip code *)
Lemma bit_flip_enc_ok i j k : bit_flip_enc Co ¦i,j,k⟩ = ¦i, i + j, i + k⟩.
Proof.
rewrite /=.
rewrite focus_dpbasis.
simpl_extract.
rewrite cnotE.
rewrite dpmerge_dpbasis.
simpl_merge.
rewrite focus_dpbasis.
simpl_extract.
rewrite cnotE dpmerge_dpbasis.
by simpl_merge.
Qed.

Lemma bit_flip_toffoli :
  (bit_flip_dec \v bit_flip_enc) =e focus [lens 1; 2; 0] toffoli.
Proof.
apply/lift_mor_eq => v.
rewrite (decompose_dpower v) !linear_sum.
apply eq_bigr => -[[|i [|j [|k []]]] Hi] _ //.
simpl_tuple (Tuple Hi).
rewrite dpmap_scale !linearZ_LR /bit_flip_dec 2!comp_morE 2!bit_flip_enc_ok.
by rewrite !addrA !addii !add0r.
Qed.

Lemma toffoli_involutive : toffoli \v toffoli =e idmor I C 3.
Proof.
apply/lift_mor_eq => v.
rewrite (decompose_dpower v) !linear_sum.
apply eq_bigr => -[[|i [|j [|k []]]] Hi] _ //.
simpl_tuple (Tuple Hi).
by rewrite dpmap_scale !linearZ_LR comp_morE !toffoliE addrA addii add0r.
Qed.

(* Not used
Lemma hadamard0E :
  hadamard Co ¦ 0 ⟩ =
  (1 / Num.sqrt 2)%:C *: \sum_(vi : 1.-tuple I) (dpbasis C vi).
Proof.
apply/ffunP => vi.
rewrite dpmorE sum_dpbasisKo !ffunE !eq_ord_tuple /= !scaler0 !addr0 !subr0.
rewrite ![_ *: 1]mulr1 !linE /= sum_ffun ffunE.
have -> : \sum_i dpbasis C i vi = \sum_i [ffun _ => 1] i *: dpbasis C vi i.
  by apply eq_bigr=> i _; rewrite ffunE scale1r dpbasisC.
rewrite sum_dpbasisKo ffunE.
have := mem_enum_indices vi; rewrite !inE => /orP[] /eqP -> /=;
by rewrite linE [_ *: 1]mulr1.
Qed.

Definition parity n (vi : n.-tuple I) : nat :=
  \sum_(i <- vi) i.

Lemma hadamard1E :
  hadamard Co ¦ 1 ⟩ =
  (1 / Num.sqrt 2)%:C *:
  \sum_(vi : 1.-tuple I) (-1)^+ (parity vi) *: dpbasis C vi.
Proof.
apply/ffunP => vi.
rewrite dpmorE sum_dpbasisKo !ffunE !eq_ord_tuple /= !scaler0 !linE.
rewrite ![_ *: 1]mulr1 /= sum_ffun ffunE.
have -> : \sum_i ((-1) ^+ parity i *: dpbasis C i) vi
          = \sum_i [ffun i => (-1) ^+ parity i] i *: dpbasis C vi i.
  by apply eq_bigr => i _; rewrite 2!ffunE dpbasisC.
rewrite sum_dpbasisKo ffunE /parity.
have := mem_enum_indices vi; rewrite !inE => /orP[] /eqP -> /=.
- by rewrite BigOp.bigopE /= expr0 subr0 [_ *: 1]mulr1.
- by rewrite BigOp.bigopE /= expr1 sub0r.
Qed.
*)

(* sign flip code *)
Lemma sign_flip_toffoli :
  (sign_flip_dec \v sign_flip_enc) =e focus [lens 1; 2; 0] toffoli.
Proof.
rewrite /sign_flip_dec /sign_flip_enc => T v /=.
rewrite [focus [lens 0] hadamard _ _]focusC /=; last by rewrite disjoint_has.
rewrite [focus [lens 0] hadamard _ _]focusC /=; last by rewrite disjoint_has.
rewrite [focus [lens 1] hadamard _ _]focusC /=; last by rewrite disjoint_has.
have HK (l : lens 3 1) : focus l hadamard \v focus l hadamard =e idmor I C 3.
  move=> U w.
  rewrite -focus_comp (focus_eq l (f2:=idmor I C 1)) ?focus_idmor //.
  exact/hadamardK.
rewrite [focus [lens 0] hadamard _ _]HK.
rewrite [focus [lens 1] hadamard _ _]HK.
rewrite [focus [lens 2] hadamard _ _]HK.
by rewrite -[RHS]bit_flip_toffoli.
Qed.

(* Shor code on a perfect channel *)
Let shor_input (i:I) := [tuple of [:: i; 0; 0; 0; 0; 0; 0; 0; 0]].
Lemma shor_code_id i :
 shor_code (idmor I C 9) Co (dpbasis C (shor_input i)) =
 dpbasis C (shor_input i).
Proof.
rewrite /=.
transitivity (focus [lens 0; 3; 6]
                    (sign_flip_dec \v sign_flip_enc)
                    Co
                    (dpbasis C (shor_input i))).
  rewrite [RHS]focus_comp /= focus_dpbasis.
  simpl_extract.
  set sfe := sign_flip_enc _ _.
  rewrite (decompose_scaler sfe).
  rewrite linear_sum.
  rewrite !linear_sum.
  (*rewrite -big_filter.*)
  apply eq_bigr => j _.
  rewrite linearZ_LR.
  rewrite 8!linearZ_LR.
  congr (_ *: focus _ _ _ _). (* i.e. congr GRing.scale *)
  rewrite dpmerge_dpbasis.
  case: j => -[|a [|b [|c []]]] Hj //=.
  simpl_merge.
  rewrite [focus [lens 6; 7; 8] bit_flip_dec _ _]focusC ?disjoint_has //=.
  rewrite [focus [lens 6; 7; 8] bit_flip_dec _ _]focusC ?disjoint_has //=.
  rewrite [focus [lens 3; 4; 5] bit_flip_dec _ _]focusC ?disjoint_has //=.
  rewrite -3![focus _ bit_flip_dec _ _]focus_comp.
  rewrite 3!(focus_eq _ bit_flip_toffoli).
  rewrite -3![focus (mkLens _) _ _ _]focusM.
  do 3 simpl_lens_comp.
  rewrite focus_dpbasis_id; last first.
    simpl_extract.
    rewrite toffoliE.
    by rewrite !linE.
  by do 2!(rewrite focus_dpbasis_id;
           last by simpl_extract; rewrite toffoliE !linE).
rewrite focus_dpbasis_id //.
simpl_extract.
rewrite sign_flip_toffoli focus_dpbasis_id //.
simpl_extract.
by rewrite toffoliE !linE.
Qed.

End shor_code.
