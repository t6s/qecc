From Stdlib Require Import Recdef Wf_nat.
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
apply: eq_lens_tnth => j; rewrite tnth_comp tnth_lensC_single.
apply/val_inj; rewrite [LHS]lift_max -tnth_map -[RHS]tnth_map.
by congr tnth; apply/val_inj.
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
apply eq_from_tnth => i; rewrite merge_extractC tnth_injectE !tnth_mktuple.
case: sumbool_of_bool => Hi.
- by rewrite -[RHS](tnth_mktuple (fun=>1) (lens_index Hi)); congr tnth; eq_lens.
- rewrite ifT //.
  by apply: contraFN Hi => Hi; rewrite !inE orbC -(inj_eq val_inj) Hi.
Qed.

(* Yet another solution using O(log n) nesting of gates *)
Definition cast_endo m1 m2 (H : m1 = m2) : endo m1 -> endo m2 :=
  cast_mor H H.

Definition lens_0_mid m : lens m.+3 2 :=
  @lens_pair _ ord0 (Ordinal (leq_half m : m./2.+2 < m.+3)%N) isT.

Function cnot_tree n {wf lt n} : endo n.+1 :=
  match n as n return endo n.+1 with
  | 0 => idmor I C 1
  | 1 => cnot
  | m.+2 => 
      cast_endo (add_uphalf_half m.+3)
        (focus (lens_left _ _) (cnot_tree ((half m).+1)) \v
           focus (lens_right _ _) (cnot_tree (half m.+1)))
      \v focus (lens_0_mid m) cnot
  end.
- move=> * /=; apply/ltP; by rewrite uphalfE ltnS leq_half.
- move=> * /=; apply/ltP; by rewrite !ltnS leq_half.
- exact: lt_wf.
Defined.

Definition ghz_tree n : endo n.+1 :=
  cnot_tree n \v focus (lens_single ord0) hadamard.

Lemma mem_lens_0_mid n (i : 'I_(uphalf n.+3 + half n.+3)) :
  (i \in [:: lshift (half n.+3) 0; rshift (uphalf n.+3) 0]) =
  (val i \in map val (lens_0_mid n)).
Proof. by rewrite !inE -2!(inj_eq val_inj) /= addn0. Qed.

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
    rewrite dpmor_dpbasis !(ffunE,tnth_mktuple,tnth_map) /= addr0.
    by congr dpbasis; eq_lens.
  rewrite dpmerge_dpbasis merge_extractC dpcast_dpbasis.
  pose mp3 := uphalf n.+3 + half n.+3.
  rewrite (_ : cast_tuple _ _ =
               [tuple if i \in [:: lshift (half n.+3) 0; rshift (uphalf n.+3) 0]
                      then b else 0 | i < mp3]); last first.
    apply/eq_from_tnth => j.
    have jn3 : (j < n.+3)%N by rewrite -[n.+3]add_uphalf_half.
    rewrite tnth_cast_tuple tnth_mktuple mem_lens_0_mid /= tnth_injectE.
    case: sumbool_of_bool => Hj; first by rewrite tnth_mktuple ifT.
    rewrite ifF // tnth_mktuple ifF //.
    by apply: contraFF Hj; rewrite inE => ->.
  rewrite focus_dpbasis.
  rewrite (_ : extract _ _ = [tuple if i == 0 then b else 0|i < _]); last first.
    apply: eq_from_tnth => j; rewrite tnth_extract.
    by rewrite !tnth_mktuple !inE eq_rlshift /= (inj_eq (@rshift_inj _ _)).
  rewrite IH; last by rewrite uphalfE ltnS leq_half.
  rewrite dpmerge_dpbasis focus_dpbasis.
  rewrite extract_merge_disjoint;
    last by rewrite disjoint_sym lens_left_right_disjoint.
  rewrite (_ : extract _ _ = [tuple if i == 0 then b else 0|i < _]); last first.
    apply: eq_from_tnth => j; rewrite tnth_extract.
    by rewrite !tnth_mktuple !inE eq_lrshift orbF (inj_eq (@lshift_inj _ _)).
  rewrite IH; last by rewrite !ltnS leq_half.
  rewrite dpmerge_dpbasis.
  rewrite (_ : extract _ _ = [tuple b | _ < _]); last first.
    apply: eq_from_tnth => j; rewrite tnth_extract tnth_merge => *.
      by rewrite mem_lensE -[X in _ \in X]lensC_left mem_tnth.
    by rewrite !tnth_mktuple.
  rewrite dpcast_dpbasis merge_cst; congr dpbasis.
  by apply/eq_from_tnth => j; rewrite tnth_cast_tuple !tnth_mktuple.
Qed.

Lemma ghz_tree_ok n :
  ghz_tree n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
rewrite /ghz_tree /= focus_dpbasis.
rewrite extract_cst -ghz_state0 /ghz_state !linearE /= !dpmerge_dpbasis.
rewrite (_ : merge _ _ _ = [tuple if i == 0 then 0 else 0 | i < _]); last first.
  apply: eq_from_tnth => i; rewrite merge_extractC tnth_injectE.
  by case: sumbool_of_bool => Hi; rewrite !tnth_mktuple if_same.
rewrite (_ : merge _ _ _ = [tuple if i == 0 then 1 else 0 | i < _]); last first.
  apply: eq_from_tnth => i; rewrite merge_extractC tnth_injectE.
  case: sumbool_of_bool => Hi; rewrite !tnth_mktuple /=;
  by move: Hi; rewrite inE => ->.
by rewrite !cnot_tree_ok !linearE.
Qed.
