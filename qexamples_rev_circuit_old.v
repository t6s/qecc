From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma leq_half n : (n./2 <= n)%N.
Proof. by rewrite -{2}(odd_double_half n) -addnn addnA leq_addl. Qed.

Lemma rev_ord_neq n (i : 'I_n./2) :
  let i' := widen_ord (leq_half n) i in i' != rev_ord i'.
Proof.
rewrite /= neq_ltn.
apply/orP/or_introl => /=.
rewrite ltn_subRL -addnS.
apply (@leq_trans (n./2 + n./2)%N).
  by apply leq_add.
by rewrite -{3}(odd_double_half n) addnn leq_addl.
Qed.

Definition rev_circuit n : endo n :=
  compn_mor (fun i => mxapp (lens_pair (rev_ord_neq i)) swap) xpredT.

Lemma rev_circuitU n : unitary_mor (rev_circuit n).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. exact/unitary_focus/swapU.
Qed.

(* Direct proof *)

Lemma rev_circuit_odd n (i : 'I_n.+2) :
  i == rev_ord i ->
  (i = n./2.+1 :> nat)%N ->
  rev_circuit n.+2 =e focus (lensC (lens_single i)) (rev_circuit n.+1).
Proof.
move=> Hi Hi' T x; rewrite focus_compn_mor.
rewrite /rev_circuit.
have Hn : (n.+2)./2 = (n.+1)./2.
  rewrite (lock n.+1).
  move/eqP/(f_equal val): Hi => /= /(f_equal (addn^~ i)).
  rewrite subSS subnK; last by rewrite -ltnS ltn_ord.
  by move <-; rewrite -lock addnn uphalf_double half_double.
rewrite /compn_mor.
have Hn' : (n./2.+1 = n.+2./2)%N by [].
set f := fun j => mxapp (lens_pair (rev_ord_neq (cast_ord Hn' (inord j)))) swap.
rewrite (eq_bigr (fun j => f (val j))); last first.
  move=> j _. congr focus. congr (lens_pair (rev_ord_neq _)).
  by apply val_inj; rewrite /= inordK.
rewrite -(big_mkord xpredT f).
rewrite Hn big_mkord.
move: T x; apply /morP/eq_bigr => j _.
apply/morP => T x.
rewrite -focusM.
have -> // : lens_comp (lensC (lens_single i)) (lens_pair (rev_ord_neq j)) =
             lens_pair (rev_ord_neq (cast_ord Hn' (inord j))).
apply/val_inj/eqP; rewrite eq_ord_tuple /=; apply/eqP.
rewrite inordK; last by rewrite Hn' Hn ltn_ord.
rewrite !tnth_lensC_single /= /bump /= Hi'.
do !(congr cons).
- case Hj: (_ < _)%N => //.
  have : (n./2 < n./2)%N by rewrite (leq_trans Hj) // -ltnS Hn' Hn.
  by rewrite ltnn.
- have -> : (n./2 < n.+1 - j.+1)%N.
    rewrite -{1}(odd_double_half n.+1) -addnn addnA -{1 2}Hn /=.
    rewrite addnS subSS -addnBA. by rewrite addnAC leq_addl.
    by rewrite -ltnS Hn' Hn.
  rewrite addnBA. by rewrite add1n.
  rewrite -(odd_double_half n.+1) (@leq_trans n.+1./2) //.
  by rewrite -addnn addnA leq_addl.
Qed.

Lemma proj_focusE_swap n (i : 'I_n.+2) (v : Co ^^ n.+2) h
      (Hn : n./2.+1 = (n.+2)./2) :
  let f j := mxapp (lens_pair (rev_ord_neq (cast_ord Hn (inord j)))) swap in
  (h < n./2.+1)%N -> (n./2.+1 - h.+1)%N = i \/ (n./2.+1 - h.+1)%N = rev_ord i ->
  proj ord0 (lens_single i)
       ((\big[comp_mor(s:=n.+2)/idmor I C _]_(n./2.+1 - h <= j < n./2.+1) f j)
          Co v) =
  proj ord0 (lens_single i) v.
Proof.
move=> f Hh ih.
have : (n./2.+1 - h > i \/ n./2.+1 - h > rev_ord i)%N.
  case: ih => ih; [left | right];
  by rewrite -ih subnS prednK // ltn_subRL addn0.
elim : h Hh {ih} => [|h IH].
  by rewrite !subn0 big_geq.
move=> Hh ih.
rewrite big_nat_recl; last by rewrite subSS leq_subr.
rewrite -(big_add1 _ _ (n./2.+1 - h.+1) (n./2.+1) xpredT f).
have Hhn : (n./2.+1 - h.+1 < n.+2)%N.
  rewrite -(odd_double_half n.+2) -addnn /= addSn addnS addnA addnC ltnS.
  by rewrite (@leq_trans n./2.+1) // (leq_subr,leq_addr).
have Hhn' : ~ (n.+2 - (n./2.+1 - h.+1).+1 < n./2.+1 - h.+1)%N.
  rewrite subSS ltn_subLR; last first.
  rewrite subSS -{2}(odd_double_half n) -addnn addnC -addnS -addnA.
    by rewrite leq_subLR addnC -!addnA leq_addr.
  rewrite addnn => /half_leq.
  rewrite doubleK /= subSS.
  move/(@leq_trans _ _ n./2)/(_ (leq_subr _ _)).
  by rewrite ltnn.
rewrite comp_morE /f proj_focusE; first last.
- exact: swapU.
- rewrite disjoint_has /= orbF !inE /=.
  apply/negP => /orP[] /eqP /(f_equal val) /=; rewrite inordK;
    (try by rewrite ltnS subSS leq_subr); move => Hi'.
  + by case: ih; rewrite /= Hi' // ltnn.
  + case: ih; rewrite /= Hi' //.
    move: (@rev_ordK n.+2 (inord (rev_ord (Ordinal (ltnW Hh))))).
    by move/(f_equal val); rewrite /= inordK // => ->; rewrite ltnn.
rewrite -IH.
- by rewrite subnS prednK // ltn_subRL addn0 ltnW.
- exact: ltnW.
- by case: ih => ih; [left|right]; move: ih; rewrite !ltn_subRL addSn => /ltnW.
Qed.

Lemma proj_swapE n (i j : 'I_n.+2) (v : Co ^^ n.+2) (Hir : i != j) :
  proj ord0 (lens_single j) (mxapp (lens_pair Hir) swap Co v) =
  proj ord0 (lens_single i) v.
Proof.
have Hior : i \in lensC (lens_single j).
  by rewrite mem_lensC !inE.
have Hri : j != i by rewrite eq_sym.
have Hroi : j \in lensC (lens_single i).
  by rewrite mem_lensC !inE.
apply/ffunP => /= vi.
rewrite /= focusE !ffunE /tinner; congr sqrtc.
rewrite [LHS](reindex_merge _ ord0 (lens_single (lens_index Hior))) //.
rewrite [RHS](reindex_merge _ ord0 (lens_single (lens_index Hroi))) //.
apply eq_bigr => /= vj _.
apply eq_bigr => /= vk _.
rewrite !ffunE !mxmorE.
under eq_bigr do rewrite !ffunE.
Admitted.
(*
rewrite sum_enum_indices /= /GRing.scale !(linE,ffunE) /= !(mulr1,mulr0,linE).
rewrite /GRing.scale /=.
rewrite (merge_pair ord0 vi vj vk Hior) //.
rewrite extract_merge extractC_merge.
rewrite (merge_pair ord0 vi vj vk Hroi) //.
rewrite (merge_rev ord0 (l:=lens_pair Hri) (l':=lens_pair Hir)
          (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])) //; first last.
  by case: vi vj => -[] // a [] // sza [] [] // b [].
have := mem_enum_indices vi => /=.
have := mem_enum_indices vj => /=.
rewrite !inE.
by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
Qed.
*)

Lemma rev_circuit_ok' n (i : 'I_(n.+2)%N) v :
  proj ord0 (lens_single (rev_ord i)) (rev_circuit n.+2 Co v) =
  proj ord0 (lens_single i) v.
Proof.
case/boolP: (i == rev_ord i) => Hir.
  rewrite -(eqP Hir).
  have Hi' : (i = n./2.+1 :> nat)%N.
    move/eqP/(f_equal val)/(f_equal (addn^~ i.+1)): Hir => /=.
    rewrite subnK // addnS -addn1 -[RHS]addn1 => /eqP.
    rewrite eqn_add2r => /eqP.
    have -> : n./2.+1 = n.+2./2 by [].
    move/(f_equal succn)/(f_equal half) => <- /=.
    by rewrite addnn uphalf_double.
  rewrite (rev_circuit_odd Hir Hi').
  rewrite proj_focusE //.
  - rewrite disjoint_has -all_predC.
    apply/allP => j /=.
    by rewrite mem_lensC negbK.
  - exact: rev_circuitU. 
have Hi: ((i < n./2.+1) || (rev_ord i < n./2.+1))%N.
  case: (ltngtP i n./2.+1) => //=.
  - rewrite -{2}(odd_double_half (n.+2)) /= negbK.
    rewrite -addnn !ltnS leq_subLR addnS -addSn addnA leq_add2r => Hni.
    rewrite -[i.+1]add1n leq_add //.
    by case: (odd n).
  - move => Hni.
    rewrite Hni -{1}(odd_double_half (n.+2)).
    rewrite -addnn /= negbK addSn !addnS !subSS addnA addnK.
    move: Hni.
    rewrite -{2}(odd_double_half n).
    case Ho: (odd n) => //= Hi'.
    move/eqP: Hir; elim.
    apply/val_inj => /=.
    rewrite Hi'.
    rewrite !subSS uphalf_double.
    by rewrite -{2}(odd_double_half n) Ho -addnn !addnA addnK.
rewrite /rev_circuit.
have Hn : (n./2.+1 = n.+2./2)%N by [].
set f := fun j => mxapp (lens_pair (rev_ord_neq (cast_ord Hn (inord j)))) swap.
rewrite /compn_mor (eq_bigr (fun j => f (val j))); last first.
  move=> j _. congr focus. congr (lens_pair (rev_ord_neq _)).
  by apply val_inj => /=; rewrite inordK // Hn.
rewrite -(big_mkord xpredT f) /=.
pose h := n./2.+1.
rewrite -(congr_big_nat _ _ _ _ (subnn h) erefl
            (fun i _ => erefl) (fun i _ => erefl)).
rewrite {1}/h.
have: (h <= n./2.+1)%N by [].
have: ((n./2.+1 - h <= i) && (n./2.+1 - h <= rev_ord i))%N by rewrite subnn.
elim: h => // [|h IH] hi Hh.
  rewrite subn0 in hi.
  have : (n./2.+1 < n./2.+1)%N.
    case/andP: hi => Hin Hrin.
    by case/orP: Hi; apply leq_ltn_trans.
  by rewrite ltnn.
rewrite big_nat_recl; last by rewrite subSS leq_subr.
rewrite -(big_add1 _ _ (n./2.+1 - h.+1) (n./2.+1) xpredT f).
rewrite comp_morE /f.
rewrite subnS prednK; last by rewrite ltn_subRL addn0.
set v' := _ _ v.
rewrite -subnS.
have Hior : i \in lensC (lens_single (rev_ord i)).
  by rewrite mem_lensC mem_lensE inE Hir.
have Hroi : rev_ord i \in lensC (lens_single i).
  by rewrite mem_lensC mem_lensE inE eq_sym Hir.
have Hri : rev_ord i != rev_ord (rev_ord i) by rewrite rev_ordK eq_sym.
case/boolP: (n./2.+1 - h.+1 == i)%N => ih.
  transitivity (proj ord0 (lens_single i) v'); last first.
     by apply proj_focusE_swap => //; left; apply/eqP.
  clearbody v'.
  rewrite (eqP ih). (* -[in lens_single i](rev_ordK i).*)
  have -> : lens_pair (rev_ord_neq (cast_ord Hn (inord i))) =
            lens_pair Hir.
    by eq_lens; rewrite inordK // -(eqP ih) ltn_subLR // addSn ltnS leq_addl.
  by apply proj_swapE.
case/boolP: (n./2.+1 - h.+1 == rev_ord i)%N => rih.
  transitivity (proj ord0 (lens_single i) v'); last first.
    by apply proj_focusE_swap => //; right; apply/eqP.
  clearbody v'.
  rewrite (eqP rih) -[in RHS](rev_ordK i).
  rewrite -{2}(rev_ordK i) in Hroi.
  have -> : lens_pair (rev_ord_neq (cast_ord Hn (inord (rev_ord i)))) =
            lens_pair Hri.
    eq_lens; rewrite inordK //.
    move/eqP: rih => /= <-. by rewrite ltnS subSS leq_subr.
  apply/ffunP => vi.
  rewrite /= focusE !ffunE /tinner; congr sqrtc.
  rewrite [LHS](reindex_merge _ ord0 (lens_single (lens_index Hior))) //.
  rewrite [RHS](reindex_merge _ ord0 (lens_single (lens_index Hroi))) //.
  apply eq_bigr => vj _.
  apply eq_bigr => vk _.
  rewrite !ffunE !mxmorE.
  under eq_bigr do rewrite !ffunE.
Abort.
(*
  rewrite sum_enum_indices /= /GRing.scale !(linE,ffunE) /= !(mulr1,mulr0,linE).
  rewrite (merge_pair ord0 vi vj vk Hroi) //.
  rewrite (merge_pair ord0 vi vj vk Hior) //.
  rewrite (merge_rev ord0 (l:=lens_pair Hir) (l':=lens_pair Hri)
             (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])); first last.
  - by case: vi vj => -[] // a [] // sza [] [] // b [].
  - by rewrite /= rev_ordK.
  rewrite extract_merge extractC_merge.
  rewrite /GRing.scale /=.
  have := mem_enum_indices vi => /=.
  have := mem_enum_indices vj => /=.
  rewrite !inE.
  by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
rewrite proj_focusE; first last.
- exact: swapU.
- rewrite disjoint_has /= orbF.
  rewrite !inE /=.
  rewrite (inj_eq rev_ord_inj).
  apply/negP => /orP[] /eqP /(f_equal val) /=; rewrite inordK;
    (try by rewrite ltnS subSS leq_subr); move => Hi'.
  + by elim (negP rih); rewrite -Hi'.
  + by elim (negP ih); rewrite Hi'.
apply IH => //.
- case/andP: hi => Hin Hrin.
  apply/andP; split.
    rewrite leq_eqVlt in Hin.
    case/orP: Hin => Hin.
      by rewrite Hin in ih.
    rewrite subnS prednK // in Hin.
    by rewrite ltn_subRL addn0.
  rewrite leq_eqVlt in Hrin.
  case/orP: Hrin => Hrin.
    by rewrite Hrin in rih.
  rewrite subnS prednK // in Hrin.
  by rewrite ltn_subRL addn0.
- exact: ltnW.
Qed.
*)
