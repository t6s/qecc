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

(* Semantics of rev_circuit *)

Lemma rev_circuitU n : unitary_mor (rev_circuit n).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. exact/unitary_focus/swapU.
Qed.

Lemma neq_ord_ge2 n (i j : 'I_n) : i != j -> (n >= 2)%N.
Proof.
case: i j => i Hi [] j Hj.
rewrite ltnNge; apply contra => Hn. apply/eqP/val_inj => /=.
case: n  Hi Hj Hn => // -[] //.
by case: i j => //= -[].
Qed.

Section swap_asym_focus.
Variables (n : nat) (i j : 'I_n.+2) (Hir : i != j) (Hri : j != i).

Definition swap_asym_focus : endo n.+2 :=
  asym_focus ord0 (lens_pair (n:=2+n) Hir) (lens_pair (n:=2+n) Hri)
    (idmor I C 2).

Lemma mxapp_swap_asym_focus : mxapp (lens_pair Hir) swap =e swap_asym_focus.
Proof.
move=> T v; apply/ffunP => /= vi.
rewrite focusE !(ffunE,mxmorE) /=.
have -> : lensC (lens_pair Hri) = lensC (lens_pair Hir).
  apply/val_inj/val_inj/eq_lensC => k; by rewrite !inE orbC.
have -> : esym (addKn_any n 2 2) = erefl by apply eq_irrelevance.
rewrite cast_tupleE.
under eq_bigr do rewrite 11!ffunE.
move: (extract (lensC _) vi) => vi'.
simpl_extract.
simpl_extract.
move: (vi`_i) (vi`_j) => a b.
have := mem_enum2 b.
have := mem_enum2 a.
rewrite !inE.
set F := curry _ _ _.
have sumK : forall (vi : 2.-tuple I),
    \sum_vj (vi == vj)%:R *: F vj = F vi.
  move=> vk; rewrite -[RHS]sum_dpbasisK.
  apply eq_bigr => vj _; by rewrite !ffunE.
do 2 (case/orP => /eqP ->);
 under eq_bigr do rewrite /= !linE; by rewrite sumK !ffunE.
Qed.
End swap_asym_focus.

(* Prove spec using foc_endo *)

Section rev_circuit_fendo.
Variable n : nat.

Lemma lens_pair_rev_sorted (i : 'I_n./2) :
  lens_sorted (lens_pair (rev_ord_neq i)).
Proof.
rewrite /lens_sorted /= /ord_ltn /= (@leq_trans n./2) //.
by rewrite -{2}(odd_double_half n) leq_subRL -addnn addnA ?leq_add // ltn_addl.
Qed.

Definition fendo_swap (i : 'I_n./2) :=
  mkFoc (lens_pair_rev_sorted i) (mxmor swap).

Lemma widen_ord_inj m (H : (m <= n)%N) : injective (widen_ord H).
Proof. move=> i j /(f_equal val) /= ij; exact/val_inj/ij. Qed.

Lemma rev_ord_gt i j :
  widen_ord (leq_half n) i != rev_ord (widen_ord (leq_half n) j).
Proof.
apply/negbT/ltn_eqF/(@leq_trans n./2) => /=. exact/ltn_ord.
rewrite leq_subRL; last by exact/(leq_trans _ (@leq_half n)).
by rewrite -{3}(odd_double_half n) -addnn addnA leq_add // ltn_addl.
Qed.

Lemma all_disjoint_swap : all_disjoint fendo_swap.
Proof.
move=> i j ij.
rewrite disjoint_has /= !inE orbF.
apply/negP => /orP[] /orP[].
- move/eqP/widen_ord_inj => wij. by move/eqP: ij; elim.
- exact/negP/rev_ord_gt.
- rewrite eq_sym; exact/negP/rev_ord_gt.
- move/eqP/rev_ord_inj/widen_ord_inj => wij. by move/eqP: ij; elim.
Qed.

Lemma rev_circuit_fendo :
  rev_circuit n = fendo_mor 0 (compn_fendo 0 fendo_swap xpredT).
Proof. rewrite -compn_mor_disjoint //; exact/all_disjoint_swap. Qed.

Lemma swap_asym_focusU P : unitary_mor (compn_fendo ord0 fendo_swap P).
Proof.
apply/compn_fendo_unitary.
- by rewrite card_ord.
- exact/all_disjoint_swap.
- move=> i; exact/swapU.
Qed.
End rev_circuit_fendo.

Lemma disjoint_compn_lens_swap n i (Hi : (i < n./2)%N) :
  [disjoint foc_l (compn_fendo ord0 (@fendo_swap _) (fun j => j != Ordinal Hi))
   & lens_pair (rev_ord_neq (Ordinal Hi))].
Proof.
apply/disjointP => j; rewrite compn_mor_lens; last exact/all_disjoint_swap.
rewrite inE => /existsP[k] /andP[] /all_disjoint_swap /disjointP; exact.
Qed.

Lemma middle_half n (i : 'I_n) : i = rev_ord i -> i = n./2 :> nat.
Proof.
move/(f_equal (half \o addn^~ i.+1 \o val)) => /=.
by rewrite subnK // addnS addnn /= uphalf_double.
Qed.

Lemma rev_circuit_ok n (i : 'I_n.+2) v :
  proj 0 (lens_single (rev_ord i)) (rev_circuit n.+2 Co v) =
  proj 0 (lens_single i) v.
Proof.
rewrite rev_circuit_fendo.
(* Special case: no swapping for the middle element (n is odd) *)
case/boolP: (i == rev_ord i) => [/eqP|] Hir.
  have Hi' := middle_half Hir.
  rewrite -Hir proj_focusE //.
  - rewrite disjoint_has /= orbF.
    rewrite compn_mor_lens ?inE; last by apply all_disjoint_swap.
    apply/existsP => /= -[k].
    rewrite !inE {2}Hir (inj_eq rev_ord_inj) orbb => /eqP/(f_equal val)/= Hk.
    by move: (ltn_ord k); rewrite -Hk Hi' ltnn.
  - exact/swap_asym_focusU.
have := Hir; rewrite eq_sym => Hri.
have Hior : i \in lensC (lens_single (rev_ord i)) by rewrite mem_lensC !inE.
have Hroi : rev_ord i \in lensC (lens_single i) by rewrite mem_lensC !inE.
pose lens_ior := lens_single (lens_index Hior).
pose lens_roi := lens_single (lens_index Hroi).
(* Main case: i < rev_ord i *)
case/boolP: (i < n.+2./2)%N => Hi.
+ have Hdisj := disjoint_compn_lens_swap Hi.
  rewrite /compn_fendo (bigD1 (Ordinal Hi)) //.
  rewrite [compf_comoid _ _ _ _ _]comp_fendoC fendo_mor_comp //.
  rewrite proj_focusE; first last.
  - exact/swap_asym_focusU.
  - apply/disjointP => j; rewrite inE => /eqP ji Hj.
    move/disjointP/(_ j Hj): Hdisj.
    by rewrite !inE ji orbC -(inj_eq val_inj) eqxx.
  rewrite /fendo_mor /=.
  have -> : lens_pair (rev_ord_neq (Ordinal Hi)) = lens_pair Hir by eq_lens.
  rewrite (mxapp_swap_asym_focus Hir).
  apply/ffunP => vi; rewrite !ffunE; congr sqrtc.
  rewrite [LHS](reindex_merge _ ord0 lens_ior) //=.
  rewrite [RHS](reindex_merge _ ord0 lens_roi) //=.
  apply eq_bigr => vj _; apply eq_bigr => vk _; rewrite !ffunE.
  have -> : addKn_any n 2 2 = erefl by apply eq_irrelevance.
  rewrite !cast_tupleE merge_pair.
  have -> : lensC (lens_pair Hri) = lensC (lens_pair Hir).
    by apply/lens_inj/eq_lensC => j; rewrite !inE orbC.
  rewrite extractC_merge [in RHS]merge_pair.
  have Hris : lens_basis (lens_pair Hri) = lens_pair Hir :> seq _.
    apply/eq_lens_sorted.
    - by move=> /= j; rewrite mem_lensE mem_filter mem_enum !inE andbT orbC.
    - exact/lens_sorted_basis.
    - rewrite /lens_sorted /ord_ltn /= -{2}(odd_double_half n.+2).
      by rewrite -addnn addnA -addnBA // addnC addnA ltn_addl.
  have Hpri : lens_perm (lens_pair Hri) = [lens 1; 0].
    eq_lens; rewrite [seq_basis _]Hris /=.
    by rewrite (negbTE Hir) !eqxx.
  rewrite -[in LHS](lens_basis_perm (lens_pair Hri)).  
  rewrite (lens_inj Hris) !extract_comp extract_merge.
  rewrite -(lens_inj Hris) merge_basis Hpri.
  set ee := extract _ _.
  have -> // : ee = [tuple of vj ++ vi].
  apply/val_inj => /=; rewrite !(tnth_nth ord0) /= !(tnth_nth ord0) /=.
  clear; by case: vi vj => -[] // a [] //= _ [] [] // b [].
(* Simpler case: i > rev_ord i *)
+ have Hi' : (rev_ord i < n.+2./2)%N.
    rewrite -leqNgt in Hi.
    rewrite /= ltn_subLR; last by apply ltn_ord.
    rewrite -{1}(odd_double_half n) -addnn /= addnS ltnS.
    rewrite addnA -addSn -addSn leq_add // ltnS.
    case Hodd: (odd n) => //.
    move: Hi; rewrite leq_eqVlt => /orP[] // /eqP Hi.
    move/eqP: Hir; elim; apply/val_inj => /=.
    rewrite -Hi -{2}(odd_double_half n.+2) /=.
    by rewrite negbK -addnn addSnnS addnA addnK Hodd.
  have Hdisj := disjoint_compn_lens_swap Hi'.
  rewrite /compn_fendo (bigD1 (Ordinal Hi')) //.
  rewrite [compf_comoid _ _ _ _ _]comp_fendoC fendo_mor_comp //.
  rewrite proj_focusE; first last.
  - exact/swap_asym_focusU.
  - apply/disjointP => j; rewrite inE => /eqP ji Hj.
    move/disjointP/(_ j Hj): Hdisj.
    by rewrite !inE ji -(inj_eq val_inj) eqxx.
  rewrite /fendo_mor /=.
  have -> : lens_pair (rev_ord_neq (Ordinal Hi')) = lens_pair Hri.
    by eq_lens; move/(f_equal val): (rev_ordK i) => /= ->.
  rewrite (mxapp_swap_asym_focus Hri).
  apply/ffunP => vi; rewrite !ffunE; congr sqrtc.
  rewrite [LHS](reindex_merge _ ord0 lens_ior) //=.
  rewrite [RHS](reindex_merge _ ord0 lens_roi) //=.
  apply eq_bigr => vj _; apply eq_bigr => vk _; rewrite !ffunE.
  have -> : addKn_any n 2 2 = erefl by apply eq_irrelevance.
  rewrite !cast_tupleE 2!merge_pair.
  by rewrite extractC_merge extract_merge.
Qed.
