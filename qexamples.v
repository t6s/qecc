Require Reals.
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens tpower unitary endo_monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section gate_examples.
Import Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* Let R := [rcfType of Reals.Rdefinitions.R]. *)
Variable R : rcfType.
Let C := [comRingType of R[i]].
Let Co := [lmodType C of C^o].
Let I := [finType of 'I_2].

Notation "¦ x1 , .. , xn ⟩" :=
  (tpbasis _ [tuple of x1%:O :: .. [:: xn%:O] ..]) (at level 0).

Notation focus := (focus 0%:O).
Notation tsapp l M := (focus l (tsmor M)).
Notation tpower := (tpower I).
Notation tsquare n := (tmatrix I C n n).
Notation endo n := (mor I C n n).

Definition qnot : tsquare 1 :=
  ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩.

Definition cnot : tsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦0,1⟩ +
  ket_bra ¦1,0⟩ ¦1,1⟩ + ket_bra ¦1,1⟩ ¦1,0⟩.

Definition hadamard : tsquare 1 :=
  (1 / Num.sqrt 2%:R)%:C *:
    (ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩ - ket_bra ¦1⟩ ¦1⟩).

Definition toffoli : tsquare 3 :=
  (\sum_(k <- [:: ¦0,0,0⟩; ¦0,0,1⟩; ¦0,1,0⟩; ¦0,1,1⟩; ¦1,0,0⟩; ¦1,0,1⟩])
      ket_bra k k) +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩.
(* =
  ket_bra ¦0,0,0⟩ ¦0,0,0⟩ + ket_bra ¦0,0,1⟩ ¦0,0,1⟩ +
  ket_bra ¦0,1,0⟩ ¦0,1,0⟩ + ket_bra ¦0,1,1⟩ ¦0,1,1⟩ +
  ket_bra ¦1,0,0⟩ ¦1,0,0⟩ + ket_bra ¦1,0,1⟩ ¦1,0,1⟩ +
  ket_bra ¦1,1,0⟩ ¦1,1,1⟩ + ket_bra ¦1,1,1⟩ ¦1,1,0⟩. *)

Definition swap : tsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,0⟩ +
  ket_bra ¦1,0⟩ ¦0,1⟩ + ket_bra ¦1,1⟩ ¦1,1⟩.
Definition swap' : tsquare 2 :=
  [ffun vi => [ffun vj =>
     (tnth vi 0%O == tnth vj 1%O)%:R * (tnth vi 1%O == tnth vj 0%O)%:R]].

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

Definition hadamard2 := tensor_tsquare hadamard hadamard.

Definition cnotH : tsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,1⟩ +
  ket_bra ¦1,0⟩ ¦1,0⟩ + ket_bra ¦1,1⟩ ¦0,1⟩.

Definition cnotHe :=
  tsmor hadamard2 \v tsmor cnot \v tsmor hadamard2.

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
  compn_mor (fun i => tsapp (lens_pair (rev_ord_neq i)) swap) xpredT.

Notation enum_indices := (enum_indices enum2).
Local Definition mem_enum_indices := mem_enum_indices mem_enum2.
Local Definition eq_from_indicesP := eq_from_indicesP mem_enum2.
Local Definition uniq_enum_indices := uniq_enum_indices uniq_enum2 mem_enum2.
Local Definition sum_enum_indices := sum_enum_indices uniq_enum2 mem_enum2.

(* Semantics of rev_circuit *)
Lemma swapU : unitary_endo (tsmor swap).
Proof.
rewrite /unitary_endo /tinner /= => s t.
rewrite !sum_enum_indices /= !tsmorE.
time (rewrite !ffunE /= !linE).
rewrite !sum_tpbasisK.
by rewrite !addrA -(addrA (_ * _)) (addrC (_ * _) (_ * _)) !addrA.
Qed.

Lemma rev_circuitU n : unitary_endo (rev_circuit n).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. by apply/unitary_focus/swapU/tsmorN.
Qed.

Lemma rev_circuitN n : naturality (rev_circuit n).
Proof.
apply: big_ind.
- by apply/idmorN.
- exact: comp_naturality.
- by move=> i _;apply/focus_naturality/tsmorN.
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
  asym_focus ord0 (lens_pair (n:=2+n) Hir) (lens_pair (n:=2+n) Hri) (idmor I 2).

Lemma tsapp_swap_asym_focus : tsapp (lens_pair Hir) swap =e swap_asym_focus.
Proof.
move=> T v; apply/ffunP => /= vi.
rewrite focusE !(ffunE,tsmorE) /=.
have -> : lothers (lens_pair Hri) = lothers (lens_pair Hir).
  eq_lens.
  rewrite (eq_filter (a2:=fun j => j \notin lens_pair Hir)) // => k.
  by rewrite !inE orbC.
have -> : esym (addKn_any n 2 2) = erefl by apply eq_irrelevance.
rewrite cast_tupleE.
under eq_bigr do rewrite 11!ffunE.
move: (extract (lothers _) vi) => vi'.
have -> : extract (lens_pair Hir) vi = [tuple tnth vi i; tnth vi j].
  by apply/val_inj.
have -> : extract (lens_pair Hri) vi = [tuple tnth vi j; tnth vi i].
  by apply/val_inj.
move: (tnth vi i) (tnth vi j) => a b.
have := mem_enum2 b.
have := mem_enum2 a.
rewrite !inE.
set F := curry _ _ _.
have sumK : forall (vi : (0+2).-tuple I),
    \sum_vj (vi == vj)%:R *: F vj = F vi.
  move=> vk; rewrite -[RHS]sum_tpbasisK.
  apply eq_bigr => vj _; by rewrite !ffunE.
do 2! (case/orP => /eqP ->);
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
  mkFoc (lens_pair_rev_sorted i) (tsmorN swap).

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
  rev_circuit n = fendo_mor ord0 (compn_fendo ord0 fendo_swap xpredT).
Proof. rewrite -compn_mor_disjoint //; exact/all_disjoint_swap. Qed.

Lemma swap_asym_focusU P : unitary_endo (compn_fendo ord0 fendo_swap P).
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
move/(f_equal val)/(f_equal (addn^~ i.+1)) => /=.
rewrite subnK // addnS => /(f_equal half).
by rewrite addnn -add1n (_ : 1%N = true) // half_bit_double.
Qed.

Lemma rev_circuit_ok n (i : 'I_n.+2) v :
  proj ord0 (lens_single (rev_ord i)) (rev_circuit n.+2 Co v) =
  proj ord0 (lens_single i) v.
Proof.
rewrite rev_circuit_fendo /compn_fendo.
(* Special case: no swapping for the middle element (n is odd) *)
case/boolP: (i == rev_ord i) => [/eqP|] Hir.
  rewrite -Hir.
  have Hi' := middle_half Hir.
  rewrite proj_focusE //.
  - apply/disjointP => j.
    rewrite inE => /eqP -> {j}.
    rewrite compn_mor_lens //=; last by apply all_disjoint_swap.
    rewrite inE => /existsP [k].
    rewrite !inE => /orP[] /eqP /(f_equal val) Hk; move: (ltn_ord k).
    + rewrite Hk /= in Hi'; by rewrite Hi' ltnn.
    + move/val_inj/(f_equal (@rev_ord _))/(f_equal val): Hk.
      rewrite -Hir rev_ordK => /= <-. by rewrite Hi' ltnn.
  - exact/foc_n.
  - exact/swap_asym_focusU.
have := Hir; rewrite eq_sym => Hri.
have Hior : i \in lothers (lens_single (rev_ord i)) by rewrite mem_lothers !inE.
have Hroi : rev_ord i \in lothers (lens_single i) by rewrite mem_lothers !inE.
pose lens_ior := lens_single (lens_index Hior).
pose lens_roi := lens_single (lens_index Hroi).
(* Main case: i < rev_ord i *)
case/boolP: (i < n.+2./2)%N => Hi.
+ have Hdisj := disjoint_compn_lens_swap Hi.
  rewrite (bigD1 (Ordinal Hi)) //= comp_fendoC fendo_mor_comp //=.
  rewrite proj_focusE; first last.
  - exact/swap_asym_focusU.
  - exact/foc_n.
  - apply/disjointP => j; rewrite inE => /eqP ji Hj.
    move/disjointP/(_ j Hj): Hdisj.
    by rewrite !inE ji orbC -(inj_eq val_inj) eqxx.
  rewrite /fendo_mor /=.
  have -> : lens_pair (rev_ord_neq (Ordinal Hi)) = lens_pair Hir by eq_lens.
  rewrite (tsapp_swap_asym_focus Hir).
  apply/ffunP => vi; rewrite !ffunE; congr sqrtc.
  rewrite [LHS](reindex_merge_indices _ ord0 lens_ior) //=.
  rewrite [RHS](reindex_merge_indices _ ord0 lens_roi) //=.
  apply eq_bigr => vj _; apply eq_bigr => vk _; rewrite !ffunE.
  have -> : addKn_any n 2 2 = erefl by apply eq_irrelevance.
  rewrite !cast_tupleE merge_indices_pair.
  have -> : lothers (lens_pair Hri) = lothers (lens_pair Hir).
    by apply/lens_inj/eq_lothers => j; rewrite !inE orbC.
  rewrite extract_lothers_merge [in RHS]merge_indices_pair.
  have Hris : lens_basis (lens_pair Hri) = lens_pair Hir.
    apply/lens_inj/eq_lens_sorted.
    - move=> /= j; rewrite mem_lensE /= /seq_basis !inE.
      by rewrite mem_filter mem_enum !inE andbT orbC.
    - exact/lens_sorted_basis.
    - rewrite /lens_sorted /= /ord_ltn /= -{2}(odd_double_half n.+2).
      by rewrite -addnn addnA -addnBA // addnC addnA ltn_addl.
  have Hpri : lens_perm (lens_pair Hri) = [lens 1; 0].
    eq_lens; rewrite -map_comp /= !(tnth_nth i) /=.
    move/(f_equal (val \o val)): Hris => /= -> /=.
    by rewrite (negbTE Hir) !eqxx.
  rewrite -[in LHS](lens_basis_perm (lens_pair Hri)).  
  rewrite Hris !extract_comp extract_merge.
  rewrite -Hris merge_indices_basis Hpri.
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
  rewrite (bigD1 (Ordinal Hi')) //= comp_fendoC fendo_mor_comp //=.
  rewrite proj_focusE; first last.
  - exact/swap_asym_focusU.
  - exact/foc_n.
  - apply/disjointP => j; rewrite inE => /eqP ji Hj.
    move/disjointP/(_ j Hj): Hdisj.
    by rewrite !inE ji -(inj_eq val_inj) eqxx.
  rewrite /fendo_mor /=.
  have -> : lens_pair (rev_ord_neq (Ordinal Hi')) = lens_pair Hri.
    by eq_lens; move/(f_equal val): (rev_ordK i) => /= ->.
  rewrite (tsapp_swap_asym_focus Hri).
  apply/ffunP => vi; rewrite !ffunE; congr sqrtc.
  rewrite [LHS](reindex_merge_indices _ ord0 lens_ior) //=.
  rewrite [RHS](reindex_merge_indices _ ord0 lens_roi) //=.
  apply eq_bigr => vj _; apply eq_bigr => vk _; rewrite !ffunE.
  have -> : addKn_any n 2 2 = erefl by apply eq_irrelevance.
  rewrite !cast_tupleE 2!merge_indices_pair.
  by rewrite extract_lothers_merge extract_merge.
Qed.

(* Alternative proof using non-commutative monoid of composition  *)

Lemma focus_compn_mor n m p (l : lens m p) (F : 'I_n -> endo p) P :
  focus l (compn_mor F P) =e compn_mor (fun i => focus l (F i)) P.
Proof.
apply (big_ind2 (fun (f : endo p) (g : endo m) => focus l f =e g)) => //.
- by move=> T v; rewrite focusE /= /focus_fun curryK.
- by move=> f1 g1 f2 g2 H1 H2 T v; rewrite focus_comp /= H1 H2.
Qed.

Lemma rev_circuit_odd n (i : 'I_n.+2) :
  i == rev_ord i ->
  (i = n./2.+1 :> nat)%N ->
  rev_circuit n.+2 =e focus (lothers (lens_single i)) (rev_circuit n.+1).
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
set f := fun j => tsapp (lens_pair (rev_ord_neq (cast_ord Hn' (inord j)))) swap.
rewrite (eq_bigr (fun j => f (val j))); last first.
  move=> j _. congr focus. congr (lens_pair (rev_ord_neq _)).
  by apply val_inj; rewrite /= inordK.
rewrite -(big_mkord xpredT f).
rewrite Hn big_mkord.
move: T x; apply /morP/eq_bigr => j _.
apply/morP => T x.
rewrite -focusM; last by apply/tsmorN.
have -> // : lens_comp (lothers (lens_single i)) (lens_pair (rev_ord_neq j)) =
             lens_pair (rev_ord_neq (cast_ord Hn' (inord j))).
eq_lens. apply/eqP.
rewrite inordK; last by rewrite Hn' Hn ltn_ord.
rewrite !tnth_lothers_single /= /bump /= Hi'.
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

Lemma proj_focusE_swap n (i : 'I_n.+2) (v : tpower n.+2 Co) h
      (Hn : n./2.+1 = (n.+2)./2) :
  let f j := tsapp (lens_pair (rev_ord_neq (cast_ord Hn (inord j)))) swap in
  (h < n./2.+1)%N -> (n./2.+1 - h.+1)%N = i \/ (n./2.+1 - h.+1)%N = rev_ord i ->
  proj ord0 (lens_single i)
       ((\big[comp_mor(s:=n.+2)/idmor I _]_(n./2.+1 - h <= j < n./2.+1) f j)
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
- by apply/tsmorN.
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

Lemma proj_swapE n (i j : 'I_n.+2) (v : tpower n.+2 Co) (Hir : i != j) :
  proj ord0 (lens_single j) (tsapp (lens_pair Hir) swap Co v) =
  proj ord0 (lens_single i) v.
Proof.
have Hior : i \in lothers (lens_single j).
  by rewrite mem_lothers !inE.
have Hri : j != i by rewrite eq_sym.
have Hroi : j \in lothers (lens_single i).
  by rewrite mem_lothers !inE.
apply/ffunP => vi.
rewrite focusE !ffunE /tinner; congr sqrtc.
rewrite [LHS](reindex_merge_indices _ ord0
                                    (lens_single (lens_index Hior))) //.
rewrite [RHS](reindex_merge_indices _ ord0
                                    (lens_single (lens_index Hroi))) //.
apply eq_bigr => vj _.
apply eq_bigr => vk _.
rewrite !ffunE !tsmorE.
under eq_bigr do rewrite !ffunE.
rewrite sum_enum_indices /= /GRing.scale !(linE,ffunE) /= !(mulr1,mulr0,linE).
rewrite /GRing.scale /=.
rewrite (merge_indices_pair ord0 vi vj vk Hior) //.
rewrite extract_merge extract_lothers_merge.
rewrite (merge_indices_pair ord0 vi vj vk Hroi) //.
rewrite (merge_indices_rev ord0 (l:=lens_pair Hri) (l':=lens_pair Hir)
          (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])) //; first last.
  by case: vi vj => -[] // a [] // sza [] [] // b [].
have := mem_enum_indices vi => /=.
have := mem_enum_indices vj => /=.
rewrite !inE.
by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
Qed.

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
    by rewrite mem_others negbK.
  - exact: rev_circuitN.
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
set f := fun j => tsapp (lens_pair (rev_ord_neq (cast_ord Hn (inord j)))) swap.
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
have Hior : i \in lothers (lens_single (rev_ord i)).
  by rewrite mem_lothers mem_lensE inE Hir.
have Hroi : rev_ord i \in lothers (lens_single i).
  by rewrite mem_lothers mem_lensE inE eq_sym Hir.
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
  rewrite focusE !ffunE /tinner; congr sqrtc.
  rewrite [LHS](reindex_merge_indices _ ord0
                                      (lens_single (lens_index Hior))) //.
  rewrite [RHS](reindex_merge_indices _ ord0
                                      (lens_single (lens_index Hroi))) //.
  apply eq_bigr => vj _.
  apply eq_bigr => vk _.
  rewrite !ffunE !tsmorE.
  under eq_bigr do rewrite !ffunE.
  rewrite sum_enum_indices /= /GRing.scale !(linE,ffunE) /= !(mulr1,mulr0,linE).
  rewrite (merge_indices_pair ord0 vi vj vk Hroi) //.
  rewrite (merge_indices_pair ord0 vi vj vk Hior) //.
  rewrite (merge_indices_rev ord0 (l:=lens_pair Hir) (l':=lens_pair Hri)
             (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])); first last.
  - by case: vi vj => -[] // a [] // sza [] [] // b [].
  - by rewrite /= rev_ordK.
  rewrite extract_merge extract_lothers_merge.
  rewrite /GRing.scale /=.
  have := mem_enum_indices vi => /=.
  have := mem_enum_indices vj => /=.
  rewrite !inE.
  by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
rewrite proj_focusE; first last.
- exact: swapU.
- exact: tsmorN.
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

(* Checking equality of functions (sum of tensors) *)
Lemma cnotK : involutive (tsmor cnot Co).
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time (by rewrite !(tsmorE,linE,sum_tpbasisK,ffunE)).
(* 2.8s *)
Qed.

Lemma qnotK : involutive (tsmor qnot Co).
Proof. (* exactly the same proof *)
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: by rewrite !(tsmorE,linE,sum_tpbasisK,ffunE).
Qed.

Lemma qnotU : unitaryts qnot.
Proof.
apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
all: rewrite !(linE,sum_tpbasisK,ffunE).
all: apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
all: rewrite !(linE,sum_tpbasisK,ffunE).
all: time (rewrite !sum_enum_indices /= !ffunE /=).
all: by rewrite !linE.
Qed.

Lemma cnotU : unitary_endo (tsmor cnot).
Proof.
rewrite /unitary_endo /tinner /= => s t.
rewrite !sum_enum_indices /=.
rewrite !tsmorE.
time (rewrite !ffunE /= !linE).
rewrite !sum_tpbasisK.
by rewrite (addrC _ (_ * _)).
Qed.

Lemma sqrt_nat_unit n : (Num.sqrt n.+1%:R : R) \is a GRing.unit.
Proof. by rewrite unitf_gt0 // -sqrtr0 ltr_sqrt ltr0Sn. Qed.

Lemma nat_unit n : (n.+1%:R : R)%R \is a GRing.unit.
Proof. by rewrite unitf_gt0 // ltr0Sn. Qed.

Lemma hadamardK (T : lmodType C) : involutive (tsmor hadamard T).
Proof.
have Hnn n : n.+1%:R / n.+1%:R = 1 :>R by rewrite divrr // nat_unit.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time (do! rewrite !(linE,ffunE,tsmorE,scalerDl,sum_enum_indices) /=).
all: rewrite -mulNrn !mulr1n -!scalerA !scale1r !scalerDr !scaleN1r !scalerN.
all: rewrite !scalerA.
all: simpc.
all: rewrite !linE.
all: rewrite -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //.
1: rewrite addrCA -addrA subrr linE -scalerDl.
2: rewrite opprK addrAC !addrA subrr linE -scalerDl.
all: rewrite -mulr2n -mulr_natl -rmorphMn /=.
all: simpc.
all: by rewrite Hnn mul0r scale1r.
Qed.

Lemma hadamardU : unitaryts hadamard.
Proof. (* Fast proof using hadamardK *)
apply/unitary_invP; last exact: hadamardK.
apply/eq_from_indicesP; do !(apply/andP; split) => //=;
  apply/eqP/eq_from_indicesP; do !(apply/andP; split); apply /eqP => //=.
all: time (rewrite !ffunE /= !linE).
all: rewrite /GRing.scale /= ?mulr1 //.
by simpc.
Qed.

(* Try on a fast machine ... *)
Lemma hadamardU' : unitaryts hadamard.
Proof.
apply/eqP/eq_from_indicesP; do !(apply/andP; split) => //=;
  apply/eqP/eq_from_indicesP; do !(apply/andP; split); apply /eqP => //=.
par: time (rewrite !ffunE;
     rewrite sum_enum_indices /= !ffunE !eq_ord_tuple /= !linE;
     simpc => //;
     rewrite -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr ?ler0n //;
     by rewrite -mulr2n -mulr_natl divrr // nat_unit).
Qed.

(* The direct proof is fast but verbose *)
Lemma hadamardU_direct : unitary_endo (tsmor hadamard).
Proof.
rewrite /unitary_endo /tinner /= => s t.
rewrite !sum_enum_indices /= !tsmorE.
time (rewrite !sum_enum_indices /= !ffunE /= !linE).
rewrite /GRing.scale /= !mulr1.
rewrite mulr1n mulrN mulr1.
simpc.
rewrite !mulrDr !rmorphD !rmorphM /= !mulrDl !oppr0.
rewrite !complexr0.
rewrite !mulrA !(mulrC (_ ^*)%C) !(mulrAC _ (_ ^*)%C).
rewrite !addrA -!rmorphM !mulrN !mulNr !rmorphN /=.
rewrite -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //.
rewrite opprK.
rewrite -!(addrAC _ (_ * t [tuple 0%:O] * ((s [tuple 0%:O])^*)%C)).
rewrite -!mulrA -mulrDl addrC !addrA.
rewrite -!(addrAC _ (_ * (t [tuple 1%:O] * ((s [tuple 1%:O])^*)%C))).
rewrite -mulrDl -addrA !mulNr -opprD -addrA addrK.
by rewrite -rmorphD -mulr2n -mulr_natl divrr ?nat_unit //= !mul1r addrC.
Qed.

(*
(* Trying to check the hadamart representation of cnot... *)
Lemma cnotH_ok : tsmor cnotH Co =1 cnotHe Co.
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=; apply/eqP.
all: rewrite !(linE,tsmorE,ffunE,scalerDl,sum_enum_indices) /=.
rewrite 50!(eq_ord_tuple,linE,ffunE,scalerDl) /=.
rewrite !enum_ordinalE /=.
rewrite 50!(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite 50!(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /=.
rewrite !enum_ordinalE /= !tsmorE.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite !sum_tpbasisK !tsmorE.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite !(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite 50!(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite 50!ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite 50!(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite !(linE,ffunE,scalerDl,sum_tpbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite -!scalerA !linE.
rewrite !(scalerA,addrA,scalerDr).
(* have Hmin1 : ((1 *- 1) = -1 :> R)%R by rewrite -mulNrn. *)
rewrite !(mulrN,mulNr,mulr1,scaleNr,opprK).
rewrite -!rmorphM /= -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr.
rewrite !(addrAC _ _ (_ *: v [tuple 0%:O; 0%:O])).
rewrite -!scalerDl.
rewrite -mulr2n -!mulrSr -mulr_natl.
Abort.
*)

(* Use linearity to extra the global factor first *)
Lemma cnotH_ok' : tsmor cnotH Co =1 cnotHe Co.
Proof.
move=> v /=.
rewrite /hadamard2 /hadamard.
set hadam := (_ *: (_ + _ + _ - _))%R.
rewrite (_ : tensor_tsquare _ _ = Linear (tensor_linearl hadam) hadam) //.
rewrite linearZ_LR.
set hadam' := (_ + _ + _ - _)%R.
rewrite (_ : Linear _ _ = Linear (tensor_linearr hadam') hadam) //.
rewrite linearZ_LR scalerA.
rewrite -!rmorphM.
rewrite !mul1r -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr ?ler0n //=.
Abort.

(*
(* Checking equality of matrices *)
Lemma cnotK' : mults cnot cnot = idts _ _ _.
Proof.
apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
par: time (apply/eqP; do! rewrite !(linE,ffunE,sum_enum_indices) => //=).
(* 18s ! *)
Qed.
*)
End gate_examples.
