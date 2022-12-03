Require Reals.
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens tpower unitary.
Require Import JMeq ProofIrrelevance. (* Wooh *)

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

Definition compn_mor n m (F : 'I_n -> endo m) :=
  \big[@comp_mor I C m m m/idmor I m]_(i < n) F i.

Definition rev_circuit n : endo n :=
  compn_mor (fun i => tsapp (lens_pair (rev_ord_neq i)) swap).

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

Lemma idmorN (J : finType) T n : naturality (idmor (R:=T) J n).
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

Section lenses.
Variable n : nat.

Section lens_set.
Variable s : {set 'I_n}.

Definition set_elements := [seq i <- enum 'I_n | i \in s].

Lemma size_set_elements : size set_elements == #|s|.
Proof. by rewrite -cards_filter cardsE. Qed.

Lemma uniq_set_elements : uniq (Tuple size_set_elements).
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lens_set := mkLens uniq_set_elements.

Lemma lens_sortedP q (l : lens n q) :
  reflect (exists p, l = [seq i <- enum 'I_n | p i] :> seq _) (lens_sorted l).
Proof.
case/boolP: (lens_sorted l) => Hl; constructor.
  exists (mem l). apply/(irr_sorted_eq (leT:=ord_ltn)) => //.
  - exact/ltn_trans.
  - by move=> x; rewrite /ord_ltn /= ltnn.
  - rewrite sorted_filter //. exact/ltn_trans. exact/sorted_enum.
    by move=> i; rewrite mem_filter mem_enum andbT.
case => p Hp.
move/negP: Hl; elim.
rewrite /lens_sorted Hp sorted_filter //. exact/ltn_trans. exact/sorted_enum.
Qed.

Lemma lens_sorted_set : lens_sorted lens_set.
Proof. by apply/lens_sortedP; exists (mem s). Qed.
End lens_set.

Lemma lens_sorted_empty : lens_sorted (lens_empty n).
Proof. done. Qed.

Section lens_basis_perm.
Variables (p : nat) (l : lens n p).

Definition seq_basis := [seq i <- enum 'I_n | i \in l].
Lemma size_basis : size seq_basis == p.
Proof.
apply/eqP.
rewrite /seq_basis.
rewrite (eq_filter (a2:=mem [set i | i in l])); last first.
  move=> i. rewrite !inE.
  case: imsetP.
    by case => x Hx ->.
  by move=> Hx; apply/negP => Hi; move: Hx; elim; exists i.
rewrite (eqP (size_set_elements _)) card_imset // -[RHS](size_tuple l).
exact/card_uniqP/lens_uniq.
Qed.
Lemma uniq_basis : uniq (Tuple size_basis).
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lens_basis := mkLens uniq_basis.

Lemma lens_sorted_basis : lens_sorted lens_basis.
Proof. by apply/lens_sortedP; exists (mem l). Qed.

Lemma lens_basis_sortedE : lens_sorted l -> lens_basis = l.
Proof.
move=> H.
apply eq_lens_sorted => //; last exact/lens_sorted_basis.
by move=> j; rewrite mem_filter mem_enum /= andbT.
Qed.

Lemma perm_in_basis i : tnth l i \in lens_basis.
Proof. by rewrite mem_filter mem_tnth mem_enum. Qed.

Definition tuple_perm := [tuple lens_index (perm_in_basis i) | i < p].
Lemma uniq_perm : uniq tuple_perm.
Proof.
rewrite map_inj_uniq ?uniq_ord_tuple //.
move=> i j.
move/(f_equal (tnth lens_basis)).
rewrite /lens_index.
rewrite (tnth_nth (tnth l i)) [RHS](tnth_nth (tnth l i)) /=.
rewrite !nth_index; try apply perm_in_basis.
exact: (tnth_inj _ (lens_uniq l)).
Qed.

Definition lens_perm := mkLens uniq_perm.

Lemma lens_basis_perm : lens_comp lens_basis lens_perm = l.
Proof.
apply/eq_lens_tnth => i.
rewrite tnth_comp tnth_mktuple /=.
by rewrite (tnth_nth (tnth l i)) /= nth_index // perm_in_basis.
Qed.

Lemma lens_perm_sortedE : lens_sorted l -> lens_perm = lens_id p.
Proof.
move=> H.
apply/eq_lens_tnth => i; rewrite !tnth_mktuple !tnth_ord_tuple.
apply/val_inj => /=.
have /(f_equal (val \o val)) /= -> := lens_basis_sortedE H.
by rewrite tnth_lensK.
Qed.
End lens_basis_perm.

Section lens_cat_perm.
Variables (p q : nat) (l1 : lens n p) (l2 : lens n q).
Hypothesis H : [disjoint l1 & l2].

Definition lens_perm_left := lens_comp (lens_perm (lens_cat H)) (lens_left p q).
Definition lens_perm_right :=
  lens_comp (lens_perm (lens_cat H)) (lens_right p q).

Lemma lens_perm_disjoint : [disjoint lens_perm_left & lens_perm_right].
Proof.
rewrite !disjoint_has.
apply/negP => /hasP [/= i].
rewrite -!map_comp => /mapP [/= j] _ -> /mapP [/= k] _.
move/(tnth_inj _ (lens_uniq (lens_perm (lens_cat H))))/eqP.
by rewrite eq_lrshift.
Qed.

Lemma lens_perm_leftE :
  lens_comp (lens_basis (lens_cat H)) lens_perm_left =
  lens_comp (lens_cat H) (lens_left p q).
Proof.
by apply/eq_lens_tnth => i; rewrite !tnth_comp -tnth_comp lens_basis_perm.
Qed.

Lemma lens_perm_rightE :
  lens_comp (lens_basis (lens_cat H)) lens_perm_right =
  lens_comp (lens_cat H) (lens_right p q).
Proof.
by apply/eq_lens_tnth => i; rewrite !tnth_comp -tnth_comp lens_basis_perm.
Qed.
End lens_cat_perm.

Lemma lens_cat_emptyl m (l : lens n m) (H : [disjoint lens_empty n & l]) :
  lens_cat H = l.
Proof. by eq_lens. Qed.

Section lens_comp.
Variables (m : nat) (l : lens n m).

Lemma lens_comp1l : lens_comp (lens_id n) l = l.
Proof. by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_lens_id. Qed.

Lemma lens_compl1 : lens_comp l (lens_id m) = l.
Proof. by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_lens_id. Qed.
End lens_comp.
End lenses.

Section foc_endo.
Variables n m : nat.
Record foc_endo : Type :=
  mkFoc { foc_m : nat; foc_l : lens n foc_m; foc_s : lens_sorted foc_l;
          foc_e :> endo foc_m; foc_n : naturality foc_e }.

Definition fendo_mor f := focus (foc_l f) f.

Definition compn_foc (F : 'I_m -> foc_endo) :=
  \big[@comp_mor I C n n n/idmor I n]_(i < m) fendo_mor (F i).

Definition all_disjoint (F : 'I_m -> foc_endo) :=
  forall i j, i != j -> [disjoint foc_l (F i) & foc_l (F j)].

Lemma null_lin p q (T : lmodType C) :
  linear (fun v : tpower p T => (0 : tpower q T)).
Proof. move=> x y z; by rewrite scaler0 add0r. Qed.
Definition nullmor p q : mor I C p q := fun T => Linear (@null_lin p q T).
Lemma nullmorN p q : naturality (nullmor p q).
Proof. by move=> T1 T2 h v; apply/ffunP => vi; rewrite !ffunE linearE. Qed.

Section comoid.
Search lens_sorted.
Definition id_fendo := mkFoc (lens_sorted_empty n) (idmorN (J:=I) (n:=0)).
Definition err_fendo := mkFoc (lens_sorted_id n) (nullmorN (p:=n) n).
Definition comp_fendo (f g : foc_endo) :=
  match Bool.bool_dec [disjoint foc_l f & foc_l g] true with
  | left H =>
      mkFoc (lens_sorted_basis (lens_cat H))
       (comp_naturality
        (focus_naturality ord0 (lens_perm_left H) (foc_n (f:=f)))
        (focus_naturality ord0 (lens_perm_right H) (foc_n (f:=g))))
  | right _ => err_fendo
  end.

Lemma eq_foc_endo (f g : foc_endo) (H : foc_m f = foc_m g) :
  JMeq (foc_l f) (foc_l g) -> JMeq (foc_e f) (foc_e g) -> f = g.
Proof.
case: f g H => f_m f_l f_s f_e f_n [] g_m g_l g_s g_e g_n /= H.
move: f_l g_l f_e g_e f_s g_s f_n g_n.
case: g_m / H => f_l g_l f_e g_e f_s g_s f_n g_n Hl He.
move: f_s g_s f_n g_n.
have := JMeq_eq Hl => Hl'.
have := JMeq_eq He => He'.
case: g_l / Hl' Hl => _.
case: g_e / He' He => _ f_s g_s f_n g_n.
rewrite (proof_irrelevance (lens_sorted f_l) f_s g_s).
by rewrite (proof_irrelevance (naturality f_e) f_n g_n).
Qed.

Lemma eq_JMeq A (x y : A) : x = y -> JMeq x y.
Proof. by move=> H; case: y / H. Qed.

Lemma focus_left_idmor p q :
  focus (R:=C) (lens_left p q) (idmor I p) = idmor I (p + q).
Proof. by apply/morP => T v; rewrite focusE /= /focus_fun /= curryK. Qed.

Lemma focus_right_idmor p q :
  focus (R:=C) (lens_right p q) (idmor I q) = idmor I (p + q).
Proof. by apply/morP => T v; rewrite focusE /= /focus_fun /= curryK. Qed.

Lemma focus_lens_right0 fm (f : endo fm) (l : lens n fm) :
  naturality f -> focus (lens_right 0 fm) f = f.
Proof.
move=> Nf.
apply/morP => T v /=.
rewrite -[LHS](focusI ord0); last by apply focus_naturality.
rewrite -focusM //.
have Heid : [disjoint lens_empty fm & lens_id fm] by rewrite disjoint_has.
have -> : lens_id (0 + fm) = lens_cat Heid by eq_lens.
by rewrite -lens_comp_right focusI.
Qed.

Lemma comp_fendo1f (f : foc_endo) : comp_fendo id_fendo f = f.
Proof.
case: f => fm l Sl f Nf.
rewrite /comp_fendo /=.
case: Bool.bool_dec; last by rewrite disjoint_has.
move=> H; apply eq_foc_endo => //=; apply eq_JMeq.
- by rewrite lens_cat_emptyl lens_basis_sortedE.
- rewrite /lens_perm_left /lens_perm_right.
  rewrite lens_cat_emptyl lens_perm_sortedE // !lens_comp1l.
  by rewrite focus_left_idmor comp_mor1f focus_lens_right0.
Qed.

Lemma comp_fendoC (f g : foc_endo) : comp_fendo f g = comp_fendo g f.
Proof.
rewrite /comp_fendo /=.
case: Bool.bool_dec => H; last first.
  case: Bool.bool_dec => H' //.
  by elim H; rewrite disjoint_sym.
case: Bool.bool_dec => H'; last by elim H'; rewrite disjoint_sym.
case: f g H H' => f_m f_l f_s f_e f_n [] g_m g_l g_s g_e g_n /= H H'.
have Hm : (g_m + f_m = f_m + g_m)%N by rewrite addnC.
apply eq_foc_endo => //=.
- have -> : lens_basis (lens_cat H) =
            cast_lens (lens_basis (lens_cat H')) Hm.
    apply/val_inj/val_inj/eq_filter => /= i.
    by rewrite !mem_cat orbC.
  move: (f_m + g_m)%N Hm => q Hm.
  case: q / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- have -> : lens_perm_left H = cast_lens_ord (lens_perm_right H') Hm.
    eq_lens; apply/eqP.
    rewrite -[RHS]map_comp.
    rewrite [RHS](eq_map (f2:=@nat_of_ord _)) //.
    rewrite -map_comp -[RHS]map_comp.
    under eq_map do rewrite /= tnth_mktuple.
    under [RHS]eq_map do rewrite /= tnth_mktuple.
    rewrite -map_comp -[RHS]map_comp.
    apply eq_map => i /=.
    rewrite (tnth_nth (tnth f_l i)).
    rewrite [in RHS](tnth_nth (tnth f_l i)) /=.
    rewrite nth_cat size_tuple ltn_ord.
    rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
    congr index.
    apply eq_filter => j /=.
    by rewrite !mem_cat orbC.
  have -> : lens_perm_right H = cast_lens_ord (lens_perm_left H') Hm.
    eq_lens; apply/eqP.
    rewrite -[RHS]map_comp.
    rewrite [RHS](eq_map (f2:=@nat_of_ord _)) //.
    rewrite -map_comp -[RHS]map_comp.
    under eq_map do rewrite /= tnth_mktuple.
    under [RHS]eq_map do rewrite /= tnth_mktuple.
    rewrite -map_comp -[RHS]map_comp.
    apply eq_map => i /=.
    rewrite (tnth_nth (tnth g_l i)).
    rewrite [in RHS](tnth_nth (tnth g_l i)) /=.
    rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
    rewrite nth_cat size_tuple ltn_ord.
    congr index.
    apply eq_filter => j /=.
    by rewrite !mem_cat orbC.
  move: (f_m + g_m)%N Hm => q Hm.
  case: q / Hm; apply eq_JMeq.
  apply/morP => T v.
  by rewrite !cast_lens_ordE focusC // disjoint_sym lens_perm_disjoint.
Qed.
    
Lemma comp_fendof1 (f : foc_endo) : comp_fendo f id_fendo = f.
Proof. by rewrite comp_fendoC comp_fendo1f. Qed.

Lemma comp_fendoef (f : foc_endo) : comp_fendo err_fendo f = err_fendo.
Proof.
rewrite /comp_fendo /=.
case: Bool.bool_dec => //.
case/boolP: (foc_m f == 0%N :> nat); last first.
  move=> Hm H; elimtype False.
  case: (foc_l f) H => -[] [|a t] Hsz Hu.
    by rewrite -(eqP Hsz) eqxx in Hm.
  by rewrite disjoint_sym disjoint_has /= mem_enum.
case: f => fm l Sl e Nf /= /eqP Hl H.
have Hn : (n = n + fm)%N by rewrite Hl addn0.
apply eq_foc_endo => //=.
- have -> : lens_basis (lens_cat H) = cast_lens (lens_id n) Hn.
    eq_lens. rewrite /seq_basis.
    rewrite (eq_filter (a2:=predT)); last first.
      move=> i. by rewrite mem_cat mem_lens_full.
    by rewrite filter_predT enum_ordinalE.
  move: (n + fm)%N Hn => q Hn.
  case: q / Hn; apply eq_JMeq.
  by rewrite cast_lensE.
- set cmp := _ \v _.
  have -> : cmp = nullmor (n+fm) (n+fm).
    subst cmp; apply/morP => T v.
    apply/ffunP => vi.
    by rewrite !focusE !ffunE.
  move: (n + fm)%N Hn => q Hn.
  by case: q / Hn.
Qed.

Lemma tpcastK p q T (H : p = q) (t : tpower q T) :
  tpcast H (tpcast (esym H) t) = t.
Proof. by apply/ffunP => v; rewrite !ffunE; f_equal; apply/val_inj. Qed.

Lemma comp_fendoA : associative comp_fendo.
Proof.
move=> f g h.
rewrite {2}/comp_fendo /=.
case: Bool.bool_dec => Hg_h; last first.
  rewrite comp_fendoC comp_fendoef.
  rewrite {1}/comp_fendo.
  case: Bool.bool_dec => Hfg_h //.
  elim: Hg_h.
  rewrite disjoint_has.
  apply/negP => /hasP [/= i ig ih].
  move: Hfg_h.
  rewrite disjoint_has => /negP; elim.
  apply/hasP; exists i => //.
  rewrite /comp_fendo/=.
  case: Bool.bool_dec => Hf_g /=.
    by rewrite mem_filter mem_cat ig mem_enum orbC.
  by rewrite mem_enum.
rewrite {3}/comp_fendo /=.
case: Bool.bool_dec => Hf_g; last first.
  rewrite comp_fendoef.
  rewrite {1}/comp_fendo /=.
  case: Bool.bool_dec => Hf_gh //.
  elim: Hf_g.
  rewrite disjoint_has.
  apply/negP => /hasP [/= i i_f ig].
  move: Hf_gh.
  rewrite disjoint_has => /negP; elim.
  apply/hasP; exists i => //=.
  by rewrite mem_filter mem_cat ig mem_enum.
rewrite {1}/comp_fendo /=.
case: Bool.bool_dec => Hf_gh; last first.
  rewrite {1}/comp_fendo /=.
  case: Bool.bool_dec => Hfg_h //.
  elim: Hf_gh.
  rewrite disjoint_has.
  apply/negP => /hasP [/= i i_f].
  rewrite mem_filter mem_cat mem_enum andbT => /orP [ig|ih].
    move: (Hf_g).
    rewrite disjoint_has => /negP; elim.
    by apply/hasP; exists i.
  move: Hfg_h.
  rewrite disjoint_has => /negP; elim.
  apply/hasP; exists i => //=.
  by rewrite mem_filter mem_cat i_f mem_enum.
rewrite {1}/comp_fendo /=.
case: Bool.bool_dec => Hfg_h; last first.
  elim: Hfg_h.
  rewrite disjoint_has.
  apply/negP => /hasP [/= i].
  rewrite mem_filter mem_cat mem_enum andbT => /orP [i_f|ig] ih.
    move: Hf_gh.
    rewrite disjoint_has => /negP; elim.
    apply/hasP; exists i => //=.
    by rewrite mem_filter mem_cat ih orbC mem_enum.
  move: (Hg_h).
  rewrite disjoint_has => /negP; elim.
  by apply/hasP; exists i.
have Hm := esym (addnA (foc_m f) (foc_m g) (foc_m h)).
apply eq_foc_endo => /=.
- by rewrite addnA.
- have -> : lens_basis (lens_cat Hf_gh) =
            cast_lens (lens_basis (lens_cat Hfg_h)) Hm.
    apply/val_inj/val_inj => /=.
    apply/eq_filter => i.
    by rewrite !(mem_enum,mem_cat,mem_filter) /= !andbT !orbA.
  move: (foc_m f + (foc_m g + foc_m h))%N Hm => q Hm.
  case: q / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- case: f g h Hg_h Hf_g Hf_gh Hfg_h Hm =>
        fm fl fS fe fN [] gm gl gS ge gN [] hm hl hS he hN /=
          Hg_h Hf_g Hf_gh Hfg_h Hm.
  set lhs := _ \v _.
  set rhs := _ \v _.
  have Hrhs : forall T : lmodType C,
      linear (fun v => tpcast Hm (rhs T (tpcast (esym Hm) v))).
    clear.
    move: (fm + (gm + hm))%N Hm rhs => q Hm.
    case: q / Hm => rhs T x y z /=.
    by rewrite !tpcastE !linearE.
  have -> : lhs = fun T => Linear (Hrhs T).
    apply/morP => T v /=.
    rewrite !focus_comp /= -!focusM //.
    have <- : cast_lens_ord (lens_perm_left Hf_gh) (esym Hm) =
              lens_comp (lens_perm_left Hfg_h) (lens_perm_left Hf_g).
      eq_lens; apply/eqP. rewrite -6!map_comp.
      apply eq_map => i /=.
      rewrite !(tnth_mktuple,tnth_ord_tuple,tnth_map) /=.
      rewrite !tnth_lshift.
      rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hf_g))) tnth_lshift.
      congr index; apply eq_filter => j.
      by rewrite !(mem_cat,mem_enum,mem_filter,andbT) orbA.
    have <- : cast_lens_ord
                (lens_comp (lens_perm_right Hf_gh) (lens_perm_left Hg_h))
                (esym Hm) =
              lens_comp (lens_perm_left Hfg_h) (lens_perm_right Hf_g).
      eq_lens; apply/eqP. rewrite -7!map_comp.
      apply eq_map => i /=.
      rewrite !(tnth_mktuple,tnth_ord_tuple,tnth_map) /=.
      rewrite tnth_rshift [in RHS]tnth_lshift.
      rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hg_h))).
      rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hf_g))).
      rewrite tnth_lshift tnth_rshift.
      congr index; apply eq_filter => j.
      by rewrite !(mem_cat,mem_enum,mem_filter,andbT) orbA.
    have <- : cast_lens_ord
                (lens_comp (lens_perm_right Hf_gh) (lens_perm_right Hg_h))
                (esym Hm) =
              lens_perm_right Hfg_h.
      eq_lens; apply/eqP. rewrite -6!map_comp.
      apply eq_map => i /=.
      rewrite !(tnth_mktuple,tnth_ord_tuple,tnth_map) /=.
      rewrite tnth_rshift [in RHS]tnth_rshift.
      rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hg_h))) tnth_rshift.
      congr index; apply eq_filter => j.
      by rewrite !(mem_cat,mem_enum,mem_filter,andbT) orbA.
    clear Hrhs rhs.
    apply (can_inj (tpcastK Hm)).
    have HK := tpcastK (esym Hm).
    rewrite esymK in HK.
    rewrite {}HK.
    move: (fm + gm + hm)%N (esym Hm) => q {}Hm.
    case: q / Hm.
    by rewrite !tpcastE !cast_lens_ordE.
  clear lhs; subst rhs.
  move: (fm + (gm + hm))%N Hm Hrhs => q Hm.
  case: q / Hm => Hrhs.
  apply/eq_JMeq/morP => T v /=.
  by rewrite !tpcastE.
Qed.

Canonical compf_monoid := Monoid.Law comp_fendoA comp_fendo1f comp_fendof1.
Canonical compf_comoid := Monoid.ComLaw comp_fendoC.
End comoid.

Section compf_mor_disjoint.
Variable F : 'I_m -> foc_endo.
Hypothesis Hdisj : all_disjoint F.

Let compn_mor_F := compn_mor (fendo_mor \o F).
Let big_endo_F := \big[comp_fendo/id_fendo]_i F i.

Lemma compn_mor_disjoint_lem :
  compn_mor_F = fendo_mor big_endo_F /\
  foc_l big_endo_F =i
  (fun i => [exists j : 'I_m, (j < m)%N && (i \in foc_l (F j))]).
Proof.
pose h := m.
rewrite -{5}/h.
rewrite /compn_mor_F /big_endo_F /compn_mor /index_enum /= -enumT.
have -> : enum 'I_m = take h (enum 'I_m).
  by rewrite -[h](size_enum_ord m) take_size.
have : (h <= m)%N by [].
elim: h => [|h IH] Hh.
  rewrite take0 !big_nil.
  split.
    apply/morP => T v.
    by rewrite /fendo_mor focusE /focus_fun /= curryK.
  move=> j. rewrite -!topredE /=.
  by apply/esym/existsP => -[].
case/(_ (ltnW Hh)): IH => IHe IHl.
rewrite (take_nth (Ordinal Hh)); last by rewrite size_enum_ord.
rewrite -cats1 2!big_cat !big_seq1 /= IHe {2 4 5 6}/comp_fendo.
case: Bool.bool_dec => H.
  split.
    apply/morP => T v.
    rewrite /fendo_mor /= !focus_comp /=.
    do 2! (rewrite -focusM; last exact/foc_n).
    by rewrite lens_perm_leftE lens_perm_rightE
       -lens_comp_left -lens_comp_right.
  move=> j /=.
  rewrite mem_lensE /= mem_filter mem_cat mem_enum andbT IHl -topredE /=.
  rewrite -[RHS]topredE /=.
  apply/esym/existsP.
  case: ifPn.
    case/orP.
      case/existsP => k /andP [Hk Hjk].
      exists k. by rewrite ltnS (ltnW Hk).
    move=> Hjh.
    exists (Ordinal Hh).
    rewrite ltnS leqnn /= /is_true -Hjh.
    congr (j \in foc_l (F _)).
    apply/val_inj => /=.
    by rewrite {3}(_ : h = Ordinal Hh) // nth_ord_enum.
  move/negP => Hneg [k] /andP [Hk Hjk].
  elim: Hneg; apply/orP.
  move: Hk; rewrite ltnS leq_eqVlt => /orP [/eqP|] Hk.
    right.
    rewrite /is_true - Hjk.
    congr (j \in foc_l (F _)).
    apply/val_inj => /=.
    by rewrite -{2}Hk nth_ord_enum.
  left; apply/existsP; exists k.
  by rewrite Hk.
elim: H; rewrite disjoint_has.
apply/negP => /hasP [j].
rewrite IHl -topredE /= => /existsP [k] /andP [kh Hjk] Hjh.
have : k != nth (Ordinal Hh) (enum 'I_m) h.
  apply/negP => /eqP kh'.
  move: kh; rewrite kh'.
  have {2} -> : h = Ordinal Hh by [].
  by rewrite nth_ord_enum ltnn.
move/Hdisj.
rewrite disjoint_has => /negP; elim.
by apply/hasP; exists j.
Qed.

Lemma compn_mor_disjoint :
  compn_mor_F = fendo_mor big_endo_F.
Proof. by case: compn_mor_disjoint_lem. Qed.

Lemma compn_mor_lens :
  foc_l big_endo_F =i (fun i => [exists j, i \in foc_l (F j)]).
Proof.
case: compn_mor_disjoint_lem => _ H i; rewrite H -2!topredE /=.
by apply eq_existsb => j; rewrite ltn_ord.
Qed.
End foc_endo.
(*
Lemma compn_foc_reindex (l : lens m m) (F : 'I_m -> foc_endo n) :
  all_disjoint F ->
  compn_foc F = compn_foc (F \o tnth l).
Proof.
*)

Lemma focus_compn_mor n m p (l : lens m p) (F : 'I_n -> endo p) :
  focus l (compn_mor F) =e compn_mor (fun i => focus l (F i)).
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
rewrite -focusM; last by apply/naturalityP; esplit.
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
- by apply/naturalityP; esplit.
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
  rewrite (eqP ih) -[in lens_single i](rev_ordK i).
  rewrite -{2}(rev_ordK i) in Hroi.
  have -> : lens_pair (rev_ord_neq (cast_ord Hn (inord i))) =
            lens_pair Hir.
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
  rewrite (merge_indices_pair ord0 vi vj vk Hior) //.
  rewrite extract_merge extract_lothers_merge.
  rewrite (merge_indices_pair ord0 vi vj vk Hroi) //.
  rewrite (merge_indices_rev ord0 (l:=lens_pair Hri) (l':=lens_pair Hir)
             (vi:=[tuple of vj ++ vi]) (vj:=[tuple of vi ++ vj])); first last.
  - by case: vi vj => -[] // a [] // sza [] [] // b [].
  - by rewrite /= rev_ordK.
  have := mem_enum_indices vi => /=.
  have := mem_enum_indices vj => /=.
  rewrite !inE.
  by do 2! (case/orP => /eqP ->); rewrite /= !(mul1r,mul0r,addr0,add0r).
case/boolP: (n./2.+1 - h.+1 == rev_ord i)%N => rih.
  transitivity (proj ord0 (lens_single i) v'); last first.
    by apply proj_focusE_swap => //; right; apply/eqP.
  clearbody v'.
  rewrite (eqP rih) -[in RHS](rev_ordK i).
  rewrite -{2}(rev_ordK i) in Hroi.
  have -> : lens_pair (rev_ord_neq (cast_ord Hn (inord (rev_ord i)))) =
            lens_pair Hri.
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
