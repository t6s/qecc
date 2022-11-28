Require Reals.
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens tpower unitary.

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

Lemma uniq_pair_lens n (i j : 'I_n) :
  i != j -> uniq [:: i; j].
Proof. by rewrite /= inE andbT. Qed.

Definition pair_lens n (i j : 'I_n) (ij : i != j) : lens n 2 :=
  mkLens (uniq_pair_lens ij).

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

Definition compn_mor n m (F : 'I_n -> endo m) :=
  \big[@comp_mor I C m m m/idmor I m]_(i < n) F i.

Definition rev_circuit n : endo n :=
  compn_mor (fun i => tsapp (pair_lens (rev_ord_neq i)) swap).

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

Lemma idmorU (J : finType) (S : rcfType) n : unitary_endo (R:=S) (idmor J n).
Proof. done. Qed.

Lemma rev_circuitU n : unitary_endo (rev_circuit n).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. by apply/unitary_focus/swapU/naturalityP; esplit.
Qed.

Lemma rev_circuitN n : naturality (rev_circuit n).
Proof.
apply: big_ind.
- by apply/naturalityP; esplit => T v; rewrite idmorE.
- exact: comp_naturality.
- by move=> i _;apply/focus_naturality/naturalityP; esplit.
Qed.

(* Attempts at proving spec *)
Section monoid.
Axiom morP : forall m n (f g : mor I C m n), f =e g <-> f = g.
Variable n : nat.
Lemma comp_mor1f (f : endo n) : idmor I n \v f = f.
Proof. by apply/morP. Qed.
Lemma comp_morf1 (f : endo n) : f \v idmor I n = f.
Proof. by apply/morP . Qed.
Lemma comp_morA' : associative (@comp_mor I C n n n).
Proof. move=> f g h; apply/morP/comp_morA. Qed.
Canonical comp_monoid :=
  Monoid.Law comp_morA' comp_mor1f comp_morf1.
End monoid.

(*
Record foc_endo n : Type :=
  mkFoc { foc_m : nat; foc_l : lens n foc_m; foc_e : endo foc_m }.

Definition compn_foc n (s : seq (foc_endo n)) :=
  \big[@comp_mor I C n n n/idmor I n]_(f <- s) focus (foc_l f) (foc_e f).

Definition all_disjoint n (s : seq (foc_endo n)) :=
  pairwise (fun f g : foc_endo n => [disjoint foc_l f & foc_l g]) s.
*)
(*
Lemma compn_foc_perm n (s q : seq (foc_endo n)) :
  all_disjoint s ->
  compn_foc s = compn_foc q.
*)

Lemma focus_compn_mor n m p (l : lens m p) (F : 'I_n -> endo p) :
  focus l (compn_mor F) =e compn_mor (fun i => focus l (F i)).
Proof.
apply (big_ind2 (fun (f : endo p) (g : endo m) => focus l f =e g)) => //.
- by move=> T v; rewrite focusE /= /focus_fun curryK.
- by move=> f1 g1 f2 g2 H1 H2 T v; rewrite focus_comp /= H1 H2.
Qed.

Lemma nth_others_singleE n (i : 'I_n.+2) k : (k < n.+1)%N ->
    val (nth i (others (lens_single i)) k) = bump i k.
Proof.
elim: (n.+1) i k => {n} [|n IH] i k.
  by rewrite ltn0.
move/eqP: (size_others (lens_single i)); rewrite /others enum_ordSl.
case: k => [|k] /=; rewrite mem_lensE memtE inE.
case: (unliftP ord0 i) => [i'|] -> Hsz.
    by rewrite eq_liftF.
  by rewrite eqxx /= enum_ordSl.
case: (unliftP ord0 i) => [i'|] ->.
  rewrite ltnS => Hsz Hk.
  rewrite eq_liftF /= filter_map size_map in Hsz *.
  rewrite (nth_map i' _ (lift ord0)); last first.
    by rewrite -ltnS Hsz subn1 ltnS.
  rewrite bumpS /= /(bump 0) add1n.
  f_equal.
  rewrite (eq_filter (a2:=fun k => k \notin lens_single i')) //.
  exact: IH.
rewrite eqxx /= filter_map size_map => Hsz Hk.
rewrite (nth_map ord0 _ (lift ord0)); last by rewrite Hsz.
congr bump.
rewrite (eq_filter (a2:=predT)) //.
rewrite ltnS in Hk.
rewrite filter_predT (_ : k.+1 = lift ord0 (Ordinal Hk)) //.
by rewrite nth_ord_enum.
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
set f := fun j => tsapp (pair_lens (rev_ord_neq (cast_ord Hn' (inord j)))) swap.
rewrite (eq_bigr (fun j => f (val j))); last first.
  move=> j _. congr focus. congr (pair_lens (rev_ord_neq _)).
  by apply val_inj; rewrite /= inordK.
rewrite -(big_mkord xpredT f).
rewrite Hn big_mkord.
move: T x; apply /morP/eq_bigr => j _.
apply/morP => T x.
rewrite -focusM; last by apply/naturalityP; esplit.
have -> // : lens_comp (lothers (lens_single i)) (pair_lens (rev_ord_neq j)) =
             pair_lens (rev_ord_neq (cast_ord Hn' (inord j))).
eq_lens. apply/eqP.
rewrite inordK; last by rewrite Hn' Hn ltn_ord.
rewrite !(tnth_nth i) /=.
have jn : (j < n)%N.
  rewrite -{2}(odd_double_half n) -addnn addnA ltn_addr //.
  by rewrite -uphalf_half ltn_ord.
rewrite !nth_others_singleE; try rewrite subSS; first last.
- by rewrite ltnS ltnW.
- by rewrite ltnS leq_subr.
- rewrite /bump.
  have /negbTE -> : ~~ (i <= j)%N by rewrite Hi' -ltnNge Hn' Hn.
have -> : (i <= n - j)%N.
  rewrite Hi' leq_subRL //=; last by rewrite ltnW.
  rewrite -{3}(odd_double_half n) -addnn addnA -addSnnS leq_add //.
  by rewrite -uphalf_half.
do !(congr cons).
by rewrite /= subSS subSn // ltnW.
Qed.

Lemma eq_lothers n m m' (l : lens n m) (l' : lens n m') :
  l =i l' -> lothers l = lothers l' :> seq _.
Proof. by move=> ll'; apply/eq_filter => i; rewrite ll'. Qed.

Section lens_comp_lothers.
Variables (n m p : nat) (l : lens n m) (l' : lens (n - m) p).

Lemma disjoint_comp_lothers : [disjoint l & lens_comp (lothers l) l'].
Proof.
rewrite disjoint_sym disjoint_has.
rewrite -all_predC.
apply/allP => i Hi /=.
apply/negP => Hi'.
move: Hi => /= /mapP [j Hj] ij.
have : i \notin l.
  by rewrite -mem_lothers ij mem_tnth.
by rewrite Hi'.
Qed.

Lemma lens_comp_lothers :
  lens_comp (lothers l) (lothers l') =
  lothers (lens_cat disjoint_comp_lothers) :> seq _.
Proof.
rewrite /= /others.
rewrite (eq_filter (a2:=preim (tnth (Tuple (size_others l)))
                    (mem (lothers (lens_comp (lothers l) l'))))); last first.
  move=> i /=.
  rewrite mem_lothers mem_lens_comp ?mem_tnth // => H.
  do 2!f_equal; apply/val_inj => /=.
  by rewrite (tnth_lensK (lothers l)).
rewrite -filter_map (_ : map _ _ = lothers l); last first.
  rewrite -(val_ord_tuple (n-m)); set mp := map _ _.
  by rewrite (_ : mp = [tuple of mp]) // -tuple_map_ord.
rewrite -filter_predI.
apply eq_filter => i /=.
by rewrite [in RHS](mem_lensE,memtE) /= mem_cat negb_or andbC mem_lothers.
Qed.
End lens_comp_lothers.

Lemma merge_indices_swap n h (i : 'I_n.+2) (vi vj : 1.-tuple I)
      (vk : (n.+2 - 1 - 1).-tuple I) (Hn : n./2.+1 = (n.+2)./2)
      (Hior : i \in lothers (lens_single (rev_ord i)))
      (Hir : i != rev_ord i) :
  (h < n./2.+1)%N ->
  merge_indices ord0 (lens_single (rev_ord i)) vi
    (merge_indices ord0 (lens_single (lens_index Hior)) vj vk) =
  merge_indices ord0 (pair_lens Hir) [tuple of vj ++ vi] vk.
Proof.
move=> Hh.
apply/eq_from_tnth => j.
rewrite !tnth_map !tnth_ord_tuple.
rewrite [index j (lens_single _)]/= [index j (pair_lens _)]/=.
case: ifP => rij.
  rewrite [X in nth _ vi X](_ : 0 = @ord0 1)%N //.
  rewrite ifF; last by rewrite -(negbTE Hir) -(eqP rij).
  case: vj => -[] // a [] //= sza.
  by rewrite -!(tnth_nth _ vi ord0).
rewrite nth_default; last by rewrite size_tuple.
have Hjl : j \in lothers (lens_single (rev_ord i)).
  by rewrite mem_lothers mem_lensE memtE inE eq_sym rij.
case: ifP => ij.
  rewrite -(eqP ij) in Hjl *.
  rewrite make_lens_index -tnth_nth.
  have -> : lens_index Hjl = lens_index Hior by apply/val_inj.
  rewrite tnth_merge_indices_single.
  by case: vj => -[].
rewrite make_lens_index -tnth_nth !tnth_map !tnth_ord_tuple.
rewrite nth_lens_out; last first.
  rewrite mem_lensE memtE inE.
  apply/negP => /eqP index_ij.
  move/negP: ij; elim.
  by rewrite -(lens_indexK Hjl) -{1}(lens_indexK Hior) /= index_ij.
rewrite [RHS]nth_default ?size_tuple //.
congr nth.
rewrite -(index_lens_comp (lothers (lens_single (lens_index Hior))) Hjl).
congr index.
rewrite lens_comp_lothers.
apply eq_lothers => /= k.
by rewrite !mem_lensE !memtE !inE lens_indexK orbC.
Qed.

Lemma proj_focusE_swap n (i : 'I_n.+2) (v : tpower n.+2 Co) h
      (Hn : n./2.+1 = (n.+2)./2) :
  (h < n./2.+1)%N -> (n./2.+1 - h.+1)%N == i ->
  proj ord0 (lens_single i)
       ((\big[comp_mor (s:=n.+2)/idmor I n.+2]_(n./2.+1 - h <= i0 < n./2.+1)
          tsapp (pair_lens (rev_ord_neq (cast_ord Hn (inord i0)))) swap) Co v) =
  proj ord0 (lens_single i) v.
Proof.
pose f := fun j : nat =>
            tsapp (pair_lens (rev_ord_neq (cast_ord Hn (inord j)))) swap.
move=> Hh ih.
have : (n./2.+1 - h > i)%N.
  by rewrite -(eqP ih) subnS prednK // ltn_subRL addn0.
elim : h Hh {ih} => [|h IH].
  by rewrite !subn0 big_geq.
move=> Hh ih.
rewrite big_nat_recl; last by rewrite subSS leq_subr.
rewrite -(big_add1 _ _ (n./2.+1 - h.+1) (n./2.+1) xpredT f).
rewrite comp_morE /f proj_focusE; first last.
- exact: swapU.
- by apply/naturalityP; esplit.
- rewrite disjoint_has /= orbF !inE /=.
  apply/negP => /orP[] /eqP /(f_equal val) /=; rewrite inordK;
    (try by rewrite ltnS subSS leq_subr); move => Hi'.
  + by rewrite Hi' ltnn in ih.
  + move: ih; rewrite Hi'.
    rewrite subSS ltn_subLR; last first.
    rewrite subSS -{2}(odd_double_half n) -addnn addnC -addnS -addnA.
      by rewrite leq_subLR addnC -!addnA leq_addr.
    rewrite addnn => /half_leq.
    rewrite doubleK /= subSS.
    move/(@leq_trans _ _ n./2)/(_ (leq_subr _ _)).
    by rewrite ltnn.
rewrite -IH.
- by rewrite subnS prednK // ltn_subRL addn0 ltnW.
- exact: ltnW.
- by move: ih; rewrite !ltn_subRL addSn => /ltnW.
Qed.

Lemma proj_focusE_swap' n (i : 'I_n.+2) (v : tpower n.+2 Co) h
      (Hn : n./2.+1 = (n.+2)./2) :
  (h < n./2.+1)%N -> (n./2.+1 - h.+1)%N == rev_ord i ->
  proj ord0 (lens_single i)
       ((\big[comp_mor (s:=n.+2)/idmor I n.+2]_(n./2.+1 - h <= i0 < n./2.+1)
          tsapp (pair_lens (rev_ord_neq (cast_ord Hn (inord i0)))) swap) Co v) =
  proj ord0 (lens_single i) v.
Proof.
pose f := fun j : nat =>
            tsapp (pair_lens (rev_ord_neq (cast_ord Hn (inord j)))) swap.
move=> Hh ih.
have : (n./2.+1 - h > rev_ord i)%N.
  by rewrite -(eqP ih) subnS prednK // ltn_subRL addn0.
elim : h Hh {ih} => [|h IH].
  by rewrite !subn0 big_geq.
move=> Hh ih.
rewrite big_nat_recl; last by rewrite subSS leq_subr.
rewrite -(big_add1 _ _ (n./2.+1 - h.+1) (n./2.+1) xpredT f).
rewrite comp_morE /f proj_focusE; first last.
- exact: swapU.
- by apply/naturalityP; esplit.
- rewrite disjoint_has /= orbF !inE /=.
  apply/negP => /orP[] /eqP /(f_equal val) /=; rewrite inordK;
    (try by rewrite ltnS subSS leq_subr); move => Hi'.
  + move: ih; rewrite /= Hi' -(odd_double_half n.+2) -addnn.
    rewrite /= addSn addnS negbK subSS addnA subnBA; last by apply ltnW.
    rewrite addnAC addnK ltn_subRL.
    rewrite ltnNge (addnC (odd n)) !addnA (addnC _ n./2) -(addSnnS n./2).
    by rewrite -!addnA leq_addr.
  +  move: ih; rewrite /= Hi'.
     rewrite !subSS subKn. by rewrite ltnn.
     rewrite -{2}(odd_double_half n) -addnn.
     apply (leq_trans (leq_subr _ _)).
     by rewrite addnA -addSn leq_addl.
rewrite -IH.
- by rewrite subnS prednK // ltn_subRL addn0 ltnW.
- exact: ltnW.
- by move: ih; rewrite !ltn_subRL addSn => /ltnW.
Qed.

Lemma mem_lens_full n i (l : lens n n) : i \in l.
Proof.
move/card_uniqP: (lens_uniq l) (cardC (mem l)) ->.
rewrite card_ord size_tuple => /(f_equal (subn^~ n)).
rewrite addKn subnn => /card0_eq/(_ i).
by rewrite !inE => /negbFE.
Qed.

Lemma merge_indices_perm (A : eqType) (dI : A) n m (l : lens n m)
      (l' : lens m m) (vi : m.-tuple A) vk :
  merge_indices dI (lens_comp l l') (extract l' vi) vk =
  merge_indices dI l vi vk.
Proof.
apply/eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple.
case/boolP: (i \in l) => Hil.
  rewrite (make_lens_index Hil) index_lens_comp.
  have Hil' : lens_index Hil \in l' by apply mem_lens_full.
  by rewrite nth_extract_index // -tnth_nth.
rewrite nth_lens_out.
  have -> : lothers (lens_comp l l') = lothers l.
    apply/val_inj/val_inj/eq_lothers => j.
    rewrite !mem_lensE !memtE /=.
    apply/mapP.
    case: ifPn => jl.
      exists (lens_index jl).
      apply mem_lens_full.
      by rewrite lens_indexK.
    case=> k Hk Hj.
    by rewrite Hj mem_tnth in jl.
  by rewrite [RHS]nth_lens_out.
apply/negP.
rewrite !mem_lensE !memtE /= => /mapP [j] Hj Hi.
by rewrite Hi mem_tnth in Hil.
Qed.

Lemma uniq_lens_rev n : uniq [tuple rev_ord i | i < n].
Proof.
rewrite (map_uniq (f:=@rev_ord n)) // -map_comp (eq_map (f2:=id)).
  by rewrite map_id enum_uniq.
by move=> x /=; rewrite rev_ordK.
Qed.
Definition lens_rev n := mkLens (uniq_lens_rev n).

Lemma tnth_rev (A : eqType) n (t : n.-tuple A) i :
  tnth [tuple of rev t] (rev_ord i) = tnth t i.
Proof.
rewrite (tnth_nth (tnth t i)) [RHS](tnth_nth (tnth t i)) /=.
rewrite nth_rev /= size_tuple; last by rewrite rev_ord_proof.
by move/(f_equal val): (rev_ordK i) => /= ->.
Qed.

Lemma merge_indices_rev (A : eqType) (dI : A) n m (l l' : lens n m)
      (vi vj : m.-tuple A) vk :
  l = rev l' :> seq _ -> vi = rev vj :> seq _ ->
  merge_indices dI l vi vk = merge_indices dI l' vj vk.
Proof.
move=> Hl Hv.
rewrite -(merge_indices_perm dI l' (lens_rev m)).
f_equal.
  apply/val_inj/eq_from_tnth => i /=.
  rewrite !tnth_map tnth_ord_tuple -[LHS]tnth_rev.
  by congr tnth; apply/val_inj; rewrite /= Hl revK.
apply/eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple.
rewrite -[LHS]tnth_rev.
by congr tnth; apply/val_inj; rewrite /= Hv revK.
Qed.

Lemma rev_circuit_ok n (i : 'I_(n.+2)%N) v :
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
set f := fun j => tsapp (pair_lens (rev_ord_neq (cast_ord Hn (inord j)))) swap.
rewrite /compn_mor (eq_bigr (fun j => f (val j))); last first.
  move=> j _. congr focus. congr (pair_lens (rev_ord_neq _)).
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
  by rewrite mem_lothers mem_lensE memtE inE Hir.
have Hroi : rev_ord i \in lothers (lens_single i).
  by rewrite mem_lothers mem_lensE memtE inE eq_sym Hir.
have Hri : rev_ord i != rev_ord (rev_ord i) by rewrite rev_ordK eq_sym.
case/boolP: (n./2.+1 - h.+1 == i)%N => ih.
  transitivity (proj ord0 (lens_single i) v'); last by apply proj_focusE_swap.
  clearbody v'.
  rewrite (eqP ih) -[in lens_single i](rev_ordK i).
  rewrite -{2}(rev_ordK i) in Hroi.
  have -> : pair_lens (rev_ord_neq (cast_ord Hn (inord i))) =
            pair_lens Hir.
    by eq_lens; rewrite inordK // -(eqP ih) ltn_subLR // addSn ltnS leq_addl.
  apply/ffunP => vi.
  rewrite focusE !ffunE /tinner.
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
  rewrite (merge_indices_swap (h:=h) vi vj vk Hn Hior) //.
  rewrite extract_merge extract_lothers_merge.
  rewrite (merge_indices_swap (h:=h) vi vj vk Hn Hroi) //.
  rewrite (merge_indices_rev ord0 (l:=pair_lens Hri) (l':=pair_lens Hir)
             (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])); first last.
  - by case: vi vj => -[] // a [] // sza [] [] // b [].
  - by rewrite /= rev_ordK.
  have := mem_enum_indices vi => /=.
  have := mem_enum_indices vj => /=.
  rewrite !inE.
  by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
case/boolP: (n./2.+1 - h.+1 == rev_ord i)%N => rih.
  transitivity (proj ord0 (lens_single i) v'); last by apply proj_focusE_swap'.
  clearbody v'.
  rewrite (eqP rih) -[in RHS](rev_ordK i).
  rewrite -{2}(rev_ordK i) in Hroi.
  have -> : pair_lens (rev_ord_neq (cast_ord Hn (inord (rev_ord i)))) =
            pair_lens Hri.
    eq_lens; rewrite inordK //.
    by move/eqP: rih => /= <-; rewrite ltnS subSS leq_subr.
  apply/ffunP => vi.
  rewrite focusE !ffunE /tinner.
  rewrite [LHS](reindex_merge_indices _ ord0
                                      (lens_single (lens_index Hior))) //.
  rewrite [RHS](reindex_merge_indices _ ord0
                                      (lens_single (lens_index Hroi))) //.
  apply eq_bigr => vj _.
  apply eq_bigr => vk _.
  rewrite !ffunE !tsmorE.
  under eq_bigr do rewrite !ffunE.
  rewrite sum_enum_indices /= /GRing.scale !(linE,ffunE) /= !(mulr1,mulr0,linE).
  rewrite (merge_indices_swap (h:=h) vi vj vk Hn Hroi) //.
  rewrite (merge_indices_swap (h:=h) vi vj vk Hn Hior) //.
  rewrite (merge_indices_rev ord0 (l:=pair_lens Hir) (l':=pair_lens Hri)
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
- by apply/naturalityP; esplit.
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
