From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments ord_max : clear implicits.

Let succ_neq n (i : 'I_n) : widen_ord (leqnSn n) i != lift ord0 i.
Proof. by rewrite neq_ltn /= /bump leq0n ltnSn. Qed.

(* Specification *)
Definition ghz_state n : Co ^^ n.+1 :=
  (1 / Num.sqrt 2)%:C *:
  (dpbasis C [tuple 0 | i < n.+1] + dpbasis C [tuple 1 | i < n.+1]).

(* Recursive definition *)
(* Uses a recursive embedding through dependent pattern-matching *)
Fixpoint ghz n :=
  match n as n return endo n.+1 with
  | 0 => mxmor hadamard
  | m.+1 =>
      mxapp (lens_pair (succ_neq (ord_max m))) cnot
      \v focus (lensC (lens_single (ord_max m.+1))) (ghz m)
  end.

(* Alternative flat definition, using iterated composition *)
Definition ghz' n : endo n.+1 :=
  compn_mor (fun i : 'I_n => mxapp (lens_pair (succ_neq (rev_ord i))) cnot)
            xpredT
  \v mxapp [lens 0] hadamard.

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
rewrite (focusE _ _ (ghz n)) /= -IH.
set f := \big[_/_]_(i < n) _ \v _.
rewrite -[uncurry _ _]/(focuslin dI _ f _ v).
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

Lemma bump0n n : bump 0 n = n.+1.
Proof. by rewrite /bump leq0n. Qed.

Lemma ghz_state0 : ghz_state 0 = mxmor hadamard Co (dpbasis C [tuple 0| _ < 1]).
Proof.
apply/ffunP => /= vi.
rewrite mxmorE !{1}ffunE /= sum_enum_indices /=.
have := mem_enum_indices vi; rewrite !inE => /orP[] /eqP -> /=;
rewrite !{1}ffunE !eq_ord_tuple /= enum_ordinalE /= !linE ![_ *: 1]mulr1;
by rewrite ![_ *: 0]mulr0 !linE.
Qed.

Lemma ghz_ok n : ghz n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
elim: n => [| n IH] /=. by rewrite ghz_state0.
rewrite focus_dpbasis.
set ls := lens_single (ord_max n.+1).
rewrite extract_cst {}IH /ghz_state !linearZ_LR /=.
congr (_ *: _); rewrite !linearE /=.
set lp := lens_pair (succ_neq (ord_max n)).
congr (_ + _); rewrite dpmerge_dpbasis.
  rewrite -(extract_cst (lensC ls)) merge_extract focus_dpbasis.
  have Hex': extract lp [tuple (0:I) | _ < n.+2] = [tuple 0; 0].
    by rewrite extract_cst; eq_lens.
  by rewrite Hex' mxmor_cnot add0r dpmerge_dpbasis -Hex' merge_extract.
rewrite extract_cst.
rewrite (_ : merge _ _ _ _ =
             [tuple if i != n.+1 :> nat then 1 else 0 | i < n.+2]); last first.
  apply eq_from_tnth => i; rewrite [RHS]tnth_mktuple.
  case: ifPn => Hi.
  - rewrite tnth_merge => [|Hi']; by rewrite !(mem_lensC,inE,tnth_mktuple).
  - rewrite tnth_mergeC => [|Hi']; by rewrite !(mem_lensC,inE,tnth_mktuple).
rewrite focus_dpbasis.
rewrite (_ : extract _ _ = [tuple 1; 0]); last first.
  by eq_lens; rewrite -!tnth_nth !tnth_mktuple neq_ltn ltnSn eqxx.
rewrite mxmor_cnot addr0 dpmerge_dpbasis.
congr dpbasis.
apply eq_from_tnth => i; rewrite [RHS]tnth_mktuple.
case/boolP: (i \in lp) => Hi.
- rewrite tnth_merge -[RHS](tnth_mktuple (fun=>1) (lens_index Hi)).
  by congr tnth; eq_lens.
- rewrite -mem_lensC in Hi.
  rewrite tnth_mergeC tnth_extract tnth_mktuple tnth_lens_index ifT //.
  move: Hi; rewrite mem_lensC; apply contra => /eqP Hi.
  by rewrite !inE; apply/orP/or_intror/eqP/val_inj.
Qed.
