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
      \v focus (lens_pair (inord_succn_neq0 (leqW (leq_half m)))) cnot
  end.
- move=> * /=; apply/ltP; by rewrite uphalfE ltnS leq_half.
- move=> * /=; apply/ltP; by rewrite !ltnS leq_half.
- exact: lt_wf.
Defined.

Definition ghz_tree n : endo n.+1 :=
  cnot_tree n \v focus (lens_single ord0) hadamard.

Lemma ghz_tree_ok n :
  ghz_tree n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
elim/ltn_ind: n.
case=> [_|[_|n IH]] /=.
- rewrite (_ : lens_single _ = lens_id _); last by eq_lens.
  by rewrite focusI ghz_state0.
- rewrite cnot_tree_equation -ghz_ok /=.
  rewrite (_ : lens_pair _ = lens_id _); last by eq_lens.
  rewrite focusI.
  by congr (cnot _ (focus _ _ _ _)); eq_lens.
- rewrite cnot_tree_equation.
Abort.
