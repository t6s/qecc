From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition bit_flip_enc : endo 3 :=
  tsapp [lens 0; 2] cnot \v  tsapp [lens 0; 1] cnot.

Definition bit_flip_dec : endo 3 :=
  tsapp [lens 1; 2; 0] toffoli \v bit_flip_enc.

Definition bit_flip_code (chan : endo 3) : endo 3 :=
  bit_flip_dec \v chan \v bit_flip_enc.

Definition hadamard3 : endo 3 :=
  tsapp [lens 2] hadamard \v tsapp [lens 1] hadamard \v tsapp [lens 0] hadamard.

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
Lemma bit_flip_enc0 j k : bit_flip_enc Co ¦0,j,k⟩ = ¦0,j,k⟩.
Proof.
rewrite /=.
rewrite focus_dpbasis.
simpl_extract.
rewrite tsmor_cnot0.
rewrite dpmerge_dpbasis.
simpl_merge.
rewrite focus_dpbasis.
simpl_extract.
rewrite tsmor_cnot0 dpmerge_dpbasis.
by congr dpbasis; eq_lens.
Qed.

Lemma bit_flip_enc1 j k : bit_flip_enc Co ¦1,j,k⟩ = ¦1, flip j, flip k⟩.
Proof.
rewrite /=.
rewrite focus_dpbasis.
simpl_extract.
rewrite tsmor_cnot1.
rewrite dpmerge_dpbasis.
simpl_merge.
rewrite focus_dpbasis.
simpl_extract.
rewrite tsmor_cnot1 dpmerge_dpbasis.
by congr dpbasis; eq_lens.
Qed.

Lemma bit_flip_toffoli :
  (bit_flip_dec \v bit_flip_enc) =e tsapp [lens 1; 2; 0] toffoli.
Proof.
apply/lift_mor_eq => v.
rewrite (decompose_dpower v) !linear_sum.
apply eq_bigr => -[[|i [|j [|k []]]] Hi] _ //.
simpl_tuple (Tuple Hi).
rewrite dpmap_scale !linearZ_LR comp_morE.
have := mem_enum2 i.
rewrite !inE => /orP[] /eqP ->.
- by rewrite bit_flip_enc0 /bit_flip_dec comp_morE bit_flip_enc0.
- rewrite bit_flip_enc1 /bit_flip_dec comp_morE bit_flip_enc1.
  by rewrite ![flip _]rev_ordK.
Qed.

(* Not used
Lemma tsmor_hadamard0 :
  tsmor hadamard Co ¦ 0 ⟩ =
  (1 / Num.sqrt 2)%:C *: \sum_(vi : 1.-tuple I) (dpbasis C vi).
Proof.
apply/ffunP => vi.
rewrite tsmorE sum_dpbasisKo !ffunE !eq_ord_tuple /= !scaler0 !addr0 !subr0.
rewrite ![_ *: 1]mulr1 !linE /= sum_ffun ffunE.
have -> : \sum_i dpbasis C i vi = \sum_i [ffun _ => 1] i *: dpbasis C vi i.
  by apply eq_bigr=> i _; rewrite ffunE scale1r dpbasisC.
rewrite sum_dpbasisKo ffunE.
have := mem_enum_indices vi; rewrite !inE => /orP[] /eqP -> /=;
by rewrite linE [_ *: 1]mulr1.
Qed.

Definition parity n (vi : n.-tuple I) : nat :=
  \sum_(i <- vi) i.

Lemma tsmor_hadamard1 :
  tsmor hadamard Co ¦ 1 ⟩ =
  (1 / Num.sqrt 2)%:C *:
  \sum_(vi : 1.-tuple I) (-1)^+ (parity vi) *: dpbasis C vi.
Proof.
apply/ffunP => vi.
rewrite tsmorE sum_dpbasisKo !ffunE !eq_ord_tuple /= !scaler0 !linE.
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
  (sign_flip_dec \v sign_flip_enc) =e tsapp [lens 1; 2; 0] toffoli.
Proof.
rewrite /sign_flip_dec /sign_flip_enc => T v /=.
rewrite [tsapp [lens 0] _ _ _](focusC dI) /=; last by rewrite disjoint_has.
rewrite [tsapp [lens 0] _ _ _](focusC dI) /=; last by rewrite disjoint_has.
rewrite [tsapp [lens 1] _ _ _](focusC dI) /=; last by rewrite disjoint_has.
have HK (l : lens 3 1) : tsapp l hadamard \v tsapp l hadamard =e idmor I C 3.
  move=> {T v} T v.
  rewrite -focus_comp (focus_eq dI l (f2:=idmor I C 1)) ?focus_idmor //.
  exact/hadamardK.
rewrite [tsapp [lens 0] _ _ _]HK.
rewrite [tsapp [lens 1] _ _ _]HK.
rewrite [tsapp [lens 2] _ _ _]HK.
by rewrite -[RHS]bit_flip_toffoli.
Qed.

(* Shor code on a perfect channel *)
Let shor_input i : 9.-tuple I := [tuple of [:: i; 0; 0; 0; 0; 0; 0; 0; 0]].
Lemma shor_code_id i :
 shor_code (idmor I C 9) Co (dpbasis C (shor_input i)) =
 dpbasis C (shor_input i).
Proof.
rewrite /=.
transitivity (focus [lens 0; 3; 6] (sign_flip_dec \v sign_flip_enc) Co
                    (dpbasis C (shor_input i))).
  rewrite [RHS]focus_comp /= focus_dpbasis.
  simpl_extract.
  set sfe := sign_flip_enc _ _.
  rewrite (decompose_scaler sfe) !linear_sum /=.
  apply eq_bigr => j _.
  rewrite !linearZ_LR /= dpmerge_dpbasis.
  congr (_ *: focus _ _ _ _).
  case: j => -[|a [|b [|c []]]] Hj //=.
  simpl_merge.
  rewrite [focus [lens 6; 7; 8] _ _ _]focusC /= ; last by rewrite disjoint_has.
  rewrite [focus [lens 6; 7; 8] _ _ _]focusC /= ; last by rewrite disjoint_has.
  rewrite [focus [lens 3; 4; 5] _ _ _]focusC /= ; last by rewrite disjoint_has.
  rewrite -3![focus _ bit_flip_dec _ _]focus_comp.
  rewrite 3!(focus_eq _ _ bit_flip_toffoli).
  rewrite -!focusM.
  do 3 simpl_lens_comp.
(*  rewrite focus_dpbasis_id; last first. simpl_extract. rewrite tsmor_toffoli00. *)
  by do !(rewrite focus_dpbasis_id; last by simpl_extract;
          rewrite tsmor_toffoli00).
rewrite focus_dpbasis_id //.
simpl_extract.
rewrite sign_flip_toffoli focus_dpbasis_id //.
simpl_extract.
by rewrite tsmor_toffoli00.
Qed.
