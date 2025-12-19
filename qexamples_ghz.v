Require Import Recdef Wf_nat.
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments ord_max : clear implicits.

Definition succ_neq n (i : 'I_n) : widen_ord (leqnSn n) i != lift ord0 i.
Proof. by rewrite neq_ltn /= /bump leq0n ltnSn. Qed.

(* Specification *)
Definition ghz_state n : Co ^^ n.+1 :=
  (1 / Num.sqrt 2)%:C *:
  (dpbasis C [tuple 0 | i < n.+1] + dpbasis C [tuple 1 | i < n.+1]).

(* Recursive definition *)
(* Uses a recursive embedding through dependent pattern-matching *)
Fixpoint ghz n :=
  match n as n return endo n.+1 with
  | 0 => hadamard
  | m.+1 =>
      focus (lens_pair (succ_neq (ord_max m))) cnot
      \v focus (lensC (lens_single (ord_max m.+1))) (ghz m)
  end.

(* Alternative flat definition, using iterated composition *)
Definition ghz' n : endo n.+1 :=
  compn_mor (fun i : 'I_n => focus (lens_pair (succ_neq (rev_ord i))) cnot)
            xpredT
  \v focus [lens 0] hadamard.

(* Proof of correctness *)
Lemma ghz_def n : ghz' n =e ghz n.
Proof.
rewrite /ghz' /compn_mor.
elim: n => [|n IH] /=.
  rewrite big_pred0; last by move=> i; rewrite -(ltn_ord i) ltn0.
  rewrite comp_mor1f (_ : [lens 0] = lens_id 1); last by eq_lens.
  exact: focusI.
rewrite big_ord_recl.
move=> T v /=.
f_equal.
  do 3 f_equal; eq_lens; by rewrite subn1.
rewrite (focusE _ (ghz n)) /= -IH.
set f := \big[_/_]_(i < n) _ \v _.
rewrite -[uncurry _ _]/(focuslin _ f _ v).
rewrite -focusE /f focus_comp /= -focusM.
simpl_lens_comp.
(* rewrite (_ : lens_comp _ _ = [lens 0]);
  last by eq_lens; rewrite /= enum_ordinalE. *)
rewrite focus_compn_mor.
do 3 f_equal.
apply eq_bigr => i _; apply/morP => {}T {}v.
rewrite -focusM.
rewrite (_ : lens_comp _ _ = lens_pair (succ_neq (rev_ord (lift 0 i)))) //.
apply eq_lens_tnth => j.
rewrite tnth_comp tnth_lensC_single.
apply val_inj.
rewrite [LHS]lift_max !(tnth_nth 0) /=.
by case: j => -[|[]].
Qed.

Lemma dpbasis_single (i:I) : dpbasis C [tuple i | _ < 1] = ¦ i ⟩.
Proof. by congr dpbasis; eq_lens. Qed.

Lemma ghz_state0 : ghz_state 0 = hadamard Co (dpbasis C [tuple 0| _ < 1]).
Proof.
rewrite dpmor_dpbasis !{1}ffunE /= /ghz_state.
by rewrite !dpbasis_single !eq_ord_tuple /= enum_ordinalE /= !linE.
Qed.

Lemma ghz_ok n : ghz n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
elim: n => [| n IH] /=. by rewrite ghz_state0.
set lp := lens_pair (succ_neq (ord_max n)).
set ls := lens_single (ord_max n.+1).
rewrite focus_dpbasis extract_cst {}IH /ghz_state !linearZ_LR /=.
congr (_ *: _); rewrite !linearE /=.
congr (_ + _); rewrite dpmerge_dpbasis.
  rewrite -(extract_cst (lensC ls)) merge_extract focus_dpbasis.
  have Hex': extract lp [tuple (0:I) | _ < n.+2] = [tuple 0; 0].
    by rewrite extract_cst; eq_lens.
  by rewrite Hex' cnotE add0r dpmerge_dpbasis -Hex' merge_extract.
rewrite extract_cst.
rewrite (_ : merge _ _ _ =
             [tuple if i != n.+1 :> nat then 1 else 0 | i < n.+2]); last first.
  apply eq_from_tnth => i; rewrite [RHS]tnth_mktuple.
  case: ifPn => Hi.
  - rewrite tnth_merge => [|Hi']; by rewrite !(mem_lensC,inE,tnth_mktuple).
  - rewrite tnth_mergeC => [|Hi']; by rewrite !(mem_lensC,inE,tnth_mktuple).
rewrite focus_dpbasis.
rewrite (_ : extract _ _ = [tuple 1; 0]); last first.
  by eq_lens; rewrite -!tnth_nth !tnth_mktuple neq_ltn ltnSn eqxx.
rewrite cnotE addr0 dpmerge_dpbasis.
congr dpbasis.
apply eq_from_tnth => i; rewrite [RHS]tnth_mktuple.
(* case: tnth_mergeP => Hi ->. *)
case/boolP: (i \in lp) => Hi.
- rewrite tnth_merge -[RHS](tnth_mktuple (fun=>1) (lens_index Hi)).
  by congr tnth; eq_lens.
- rewrite -mem_lensC in Hi.
  rewrite tnth_mergeC tnth_extract tnth_mktuple.
  rewrite tnth_lens_index ifT //.
  move: Hi; rewrite mem_lensC !inE; apply contra.
  by move/eqP => Hi; apply/orP/or_intror/eqP/val_inj.
Qed.

(* Yet another solution using O(log n) gates *)
Definition cast_endo m1 m2 (H : m1 = m2) : endo m1 -> endo m2 :=
  cast_mor H H.

Lemma add_uphalf_half m : (uphalf m + half m = m)%N.
Proof. by rewrite uphalf_half -addnA addnn odd_double_half. Qed.

Lemma inord_succn_neq0 m i : (i <= m)%N -> ord0 != inord i.+1 :> 'I_m.+2.
Proof. by rewrite -2!ltnS => /inordK H; apply/eqP=>/(f_equal val)/=/[!H]. Qed.

Lemma leq_half m : (m./2 <= m)%N.
Proof. by rewrite leq_half_double -addnn -addnS leq_addr. Qed.

Function cnot_tree n {wf lt n} : endo n.+1 :=
  match n as n return endo n.+1 with
  | 0 => idmor I C 1
  | 1 => cnot
  | m.+2 => 
      cast_endo (add_uphalf_half m.+3)
        (focus (lens_left _ _) (cnot_tree ((half m).+1)) \v
           focus (lens_right _ _) (cnot_tree (half m.+1)))
      \v focus (@lens_pair m.+3 ord0 (inord (m./2.+2))
                  (inord_succn_neq0 (leq_half m : m./2 < m.+1)%N)) cnot
  end.
- move=> * /=; apply/ltP; by rewrite uphalfE ltnS leq_half.
- move=> * /=; apply/ltP; by rewrite !ltnS leq_half.
- exact: lt_wf.
Defined.

Definition ghz_tree n : endo n.+1 :=
  cnot_tree n \v focus (lens_single ord0) hadamard.

Lemma cnot_tree_ok n (b : I) :
  cnot_tree n Co (dpbasis C [tuple if i == 0 then b else 0 | i < n.+1]) =
    dpbasis C [tuple b | _ < n.+1].
Proof.
elim/ltn_ind: n.
case=> [_|[_|n IH]] /=.
- by congr dpbasis; apply eq_mktuple => -[] [].
- rewrite cnot_tree_equation dpmor_dpbasis !ffunE !tnth_mktuple /= addr0.
  by congr dpbasis; eq_lens.
- rewrite cnot_tree_equation /= focus_dpbasis.
  rewrite (_ : cnot Co _ = dpbasis C [tuple b | _ < 2]); last first.
    rewrite dpmor_dpbasis !ffunE !(tnth_mktuple,tnth_map) !(tnth_nth ord0) /=.
    rewrite ifN ?addr0.
      by congr dpbasis; eq_lens.
    apply/eqP => /(f_equal val) /=.
    by rewrite inordK // !ltnS leq_half.
  pose mp3 := uphalf n.+3 + half n.+3.
  rewrite (_ : dpcast (esym _) _ =
    dpbasis C [tuple if i \in [:: lshift (half n.+3) 0; rshift (uphalf n.+3) 0]
                     then b else 0 | i < mp3]); last first.
    rewrite dpmerge_dpbasis.
    apply/ffunP => /= v.
    rewrite !ffunE.
    rewrite -(inj_eq (f:=cast_tuple (esym(esym(add_uphalf_half n.+3)))));
      last exact/bij_inj/cast_tuple_bij.
    congr ((nat_of_bool (_ == _))%:R).
    apply/eq_from_tnth => j.
    rewrite tnth_map tnth_ord_tuple (tnth_nth 0) /= (nth_map ord0); last first.
      by rewrite size_enum_ord [X in (_ < X)%N](add_uphalf_half n.+3).
    rewrite ![in RHS]inE.
    have jmp3 : (j < mp3)%N by rewrite [mp3]add_uphalf_half.
    case: sumbool_of_bool => Hj.
      rewrite tnth_mktuple ifT //.
      apply/orP.
      move: Hj; rewrite !inE => /orP[] /eqP ->; [left | right];
        apply/eqP/val_inj; rewrite /= nth_enum_ord //.
        by rewrite addn0 inordK // !ltnS leq_half.
      by rewrite [mp3]add_uphalf_half inordK // !ltnS leq_half.
    move/negbT: (Hj); rewrite !inE negb_or => /andP[j0 j1].
    rewrite tnth_extract tnth_mktuple ifF.
      rewrite ifF //.
      apply/negbTE/negP => /orP[] /eqP /(f_equal val) /=;
        rewrite /= nth_enum_ord // ?addn0 => {}Hj.
        by move/eqP: j0; elim; apply/val_inj.
      move/eqP: j1; elim; apply/val_inj => /=.
      by rewrite inordK // !ltnS leq_half.
    move: (mem_tnth (lens_index (mem_lensFC Hj))
          (lensC (lens_pair (inord_succn_neq0 (leq_half n: n./2 < n.+1)%N)))).
    case/boolP: (_ == 0) => // /eqP ->.
    by rewrite mem_lensC !inE negb_or andbC inord_succn_neq0 // ltnS leq_half.
  rewrite focus_dpbasis.
  rewrite (_ : extract _ _ = [tuple if i == 0 then b else 0|i < (uphalf n).+1]);
    last first.
    apply: eq_from_tnth => j.
    rewrite tnth_extract !tnth_mktuple !inE eq_rlshift /=.
    by rewrite (inj_eq (@rshift_inj _ _)).
  rewrite IH; last by rewrite uphalfE ltnS leq_half.
  rewrite dpmerge_dpbasis merge_extractC focus_dpbasis.
  rewrite (_ : extract _ _ = [tuple if i == 0 then b else 0|i < n./2.+2]);
    last first.
    apply: eq_from_tnth => j.
    rewrite tnth_extract !tnth_mktuple !inE eq_lrshift orbF.
    rewrite (inj_eq (@lshift_inj _ _)) nth_lens_out //.
    apply/negP => /=.
    rewrite mem_lensE /= => /mapP[k] _ /eqP.
    by rewrite eq_lrshift.
  rewrite IH; last by rewrite !ltnS leq_half.
  rewrite dpmerge_dpbasis.
  rewrite (_ : extract _ _ = [tuple b | _ < _]); last first.
    apply: eq_from_tnth => j.
    rewrite -merge_extractC.
    rewrite tnth_extract.
    have Hj : (lensC (lens_left n./2.+2 (uphalf n).+1)) !_ j
                \in lens_right n./2.+2 (uphalf n).+1.
      rewrite mem_lensE
        (_ : \val _ = tval (lens_right n./2.+2 (uphalf n).+1)) //.
      by rewrite -lensC_left mem_tnth.
    by rewrite tnth_merge !tnth_mktuple.
  apply/ffunP => v; rewrite !ffunE.
  rewrite -(inj_eq (f:=cast_tuple (esym(add_uphalf_half n.+3))));
      last exact/bij_inj/cast_tuple_bij.
  congr ((nat_of_bool (_ == _))%:R).
  apply/eq_from_tnth => j.
  rewrite tnth_map tnth_ord_tuple (tnth_nth 0) /= (nth_map ord0); last first.
    by rewrite size_enum_ord -(add_uphalf_half n.+3).
  by case: sumbool_of_bool => Hj; rewrite tnth_mktuple.
Qed.

Lemma ghz_tree_ok n :
  ghz_tree n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
rewrite /ghz_tree /= focus_dpbasis.
rewrite extract_cst -ghz_state0 /ghz_state !linearE /= !dpmerge_dpbasis.
rewrite (_ : merge _ _ _ = [tuple if i == 0 then 0 else 0 | i < _]); last first.
  apply: eq_from_tnth => i; rewrite !tnth_mktuple.
  by case: sumbool_of_bool => Hi; rewrite !(tnth_extract,tnth_mktuple) if_same.
rewrite (_ : merge _ _ _ = [tuple if i == 0 then 1 else 0 | i < _]); last first.
  apply: eq_from_tnth => i.
  case/boolP: (i \in lens_single ord0) => Hi.
    rewrite tnth_merge !tnth_mktuple.
    by move: Hi; rewrite !inE => /eqP ->; rewrite eqxx.
  rewrite -mem_lensC in Hi.
  rewrite tnth_mergeC !tnth_extract !tnth_mktuple.
  by move: Hi; rewrite mem_lensC !inE => /negbTE ->.
by rewrite !cnot_tree_ok !linearE.
Qed.
