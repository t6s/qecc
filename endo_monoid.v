Require Reals.
From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens tpower unitary.
Require Import JMeq ProofIrrelevance FunctionalExtensionality. (* Wooh *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Section endo_monoid.
Variables (I : finType) (dI : I).

Notation focus := (focus dI).
Notation tsapp l M := (focus l (tsmor M)).
Notation tpower := (tpower I).

Section com_ring.
Variable R : comRingType.

Local Notation mor m n := (mor I R m n).
Local Notation endo n := (mor n n).

Lemma morP : forall m n (f g : mor m n), f =e g <-> f = g.
Proof.
split => [fg | -> //].
apply functional_extensionality_dep => T /=.
move/(_ T): fg.
case f => /= {}f Hf.
case g => /= {}g Hg /functional_extensionality fg.
move: Hf Hg; case: g / fg => Hf Hg.
by rewrite (proof_irrelevance (lmorphism f) Hf Hg).
Qed.

Section mor_monoid.
Variable n : nat.

Lemma comp_mor1f (f : endo n) : idmor I n \v f = f.
Proof. by apply/morP. Qed.
Lemma comp_morf1 (f : endo n) : f \v idmor I n = f.
Proof. by apply/morP . Qed.
Lemma comp_morA' : associative (@comp_mor I R n n n).
Proof. move=> f g h; apply/morP/comp_morA. Qed.
Canonical comp_monoid :=
  Monoid.Law comp_morA' comp_mor1f comp_morf1.

Definition compn_mor m (F : 'I_n -> endo m) (P : pred 'I_n) :=
  \big[@comp_mor I R m m m/idmor I m]_(i < n | P i) F i.
End mor_monoid.

Section foc_endo.
Variable n : nat.
Record foc_endo : Type :=
  mkFoc { foc_m : nat; foc_l : lens n foc_m; foc_s : lens_sorted foc_l;
          foc_e :> endo foc_m; foc_n : naturality foc_e }.

Definition fendo_mor f := focus (foc_l f) f.

Section mkFendo.
Variables (m : nat) (l : lens n m) (f : endo m) (Nf : naturality f).
Definition mkFendo :=
  mkFoc (lens_sorted_basis l) (focus_naturality dI (lens_perm l) Nf).

Lemma mkFendoE : fendo_mor mkFendo = focus l f.
Proof.
by apply/morP => T v; rewrite /fendo_mor /= -focusM // lens_basis_perm.
Qed.
End mkFendo.

Lemma null_lin p q (T : lmodType R) :
  linear (fun v : tpower p T => (0 : tpower q T)).
Proof. move=> x y z; by rewrite scaler0 add0r. Qed.
Definition nullmor p q : mor p q := fun T => Linear (@null_lin p q T).
Lemma nullmorN p q : naturality (nullmor p q).
Proof. by move=> T1 T2 h v; apply/ffunP => vi; rewrite !ffunE linearE. Qed.

Section comoid.
Definition id_fendo := mkFoc (lens_sorted_empty n) (idmorN (I:=I) (n:=0)).
Definition err_fendo := mkFoc (lens_sorted_id n) (nullmorN (p:=n) n).

Section comp_fendo.
Definition comp_fendo (f g : foc_endo) :=
  match Bool.bool_dec [disjoint foc_l f & foc_l g] true with
  | left H =>
      mkFoc (lens_sorted_basis (lens_cat H))
       (comp_naturality
        (focus_naturality dI (lens_perm_left H) (foc_n (f:=f)))
        (focus_naturality dI (lens_perm_right H) (foc_n (f:=g))))
  | right _ => err_fendo
  end.

Variables f g : foc_endo.
Lemma comp_fendo_sub : {subset foc_l f <= foc_l (comp_fendo f g)}.
Proof.
move=> i Hif.
rewrite /comp_fendo; case: Bool.bool_dec => H /=.
- by rewrite mem_lens_basis mem_cat Hif.
- by rewrite mem_lens_full.
Qed.

Lemma comp_fendo_err :
  [disjoint foc_l f & foc_l g] <> true -> comp_fendo f g = err_fendo.
Proof. by move=> H; rewrite /comp_fendo; case: Bool.bool_dec. Qed.

Hypothesis Hdisj : [disjoint foc_l f & foc_l g].
Lemma foc_l_comp_fendo :
  foc_l (comp_fendo f g) =i predU (mem (foc_l f)) (mem (foc_l g)).
Proof.
move=> i; rewrite inE /comp_fendo /=.
case: Bool.bool_dec => H; last contradiction.
by rewrite mem_lens_basis mem_cat.
Qed.

Lemma fendo_mor_comp : fendo_mor (comp_fendo f g) = fendo_mor f \v fendo_mor g.
Proof.
apply/morP => T v.
rewrite /fendo_mor /comp_fendo /=.
case: Bool.bool_dec => H /=; last contradiction.
rewrite focus_comp /= -!focusM; try exact/foc_n.
by rewrite lens_perm_leftE lens_perm_rightE -lens_comp_left -lens_comp_right.
Qed.
End comp_fendo.

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
rewrite (eq_irrelevance f_s g_s).
by rewrite (proof_irrelevance (naturality f_e) f_n g_n).
Qed.

Lemma eq_JMeq A (x y : A) : x = y -> JMeq x y.
Proof. by move=> H; case: y / H. Qed.

Lemma focus_left_idmor p q :
  focus (R:=R) (lens_left p q) (idmor I p) = idmor I (p + q).
Proof. by apply/morP => T v; rewrite focusE /= /focus_fun /= curryK. Qed.

Lemma focus_right_idmor p q :
  focus (R:=R) (lens_right p q) (idmor I q) = idmor I (p + q).
Proof. by apply/morP => T v; rewrite focusE /= /focus_fun /= curryK. Qed.

Lemma focus_lens_right0 fm (f : endo fm) (l : lens n fm) :
  naturality f -> focus (lens_right 0 fm) f = f.
Proof.
move=> Nf.
apply/morP => T v /=.
rewrite -[LHS](focusI dI); last by apply focus_naturality.
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

Lemma lens_perm_left_right m p (f : lens n m) (g : lens n p)
  (H : [disjoint f & g]) (H' : [disjoint g & f]) (Hm : (p + m = m + p)%N) :
  lens_perm_left H = cast_lens_ord (lens_perm_right H') Hm.
Proof.
eq_lens; apply/eqP.
rewrite -[RHS]map_comp [RHS](eq_map (f2:=@nat_of_ord _)) //.
rewrite -2!map_comp -2![RHS]map_comp.
apply eq_map => i /=.
rewrite !tnth_mktuple /= tnth_lshift tnth_rshift.
congr index; apply eq_filter => j /=.
by rewrite !mem_cat orbC.
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
    apply/lens_inj/eq_filter => /= i.
    by rewrite !mem_cat orbC.
  move: (f_m + g_m)%N Hm => q Hm.
  case: q / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- rewrite lens_perm_left_right.
  have -> : lens_perm_right H = cast_lens_ord (lens_perm_left H') Hm.
    rewrite (lens_perm_left_right  H' H (esym Hm)).
    by eq_lens; apply/eqP; rewrite -!map_comp /=; apply eq_map.
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
    apply/lens_inj; rewrite -[RHS]enum_filterP.
    by apply eq_filter => i; rewrite mem_cat mem_lens_full.
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

Lemma comp_fendoA : associative comp_fendo.
Proof.
move=> f g h.
rewrite {2}/comp_fendo /=.
case: Bool.bool_dec => Hg_h; last first.
  rewrite comp_fendoC comp_fendoef comp_fendo_err //= => Hfg_h.
  elim: Hg_h; apply/disjointP => i ig ih.
  move/disjointP/(_ i): Hfg_h; elim => //.
  rewrite comp_fendoC; exact/comp_fendo_sub.
rewrite {3}/comp_fendo /=.
case: Bool.bool_dec => Hf_g; last first.
  rewrite comp_fendoef comp_fendo_err //= => Hf_gh.
  elim: Hf_g; apply/disjointP => i i_f ig.
  move/disjointP/(_ i): Hf_gh; elim => //.
  by rewrite mem_lens_basis mem_cat ig.
rewrite {1}/comp_fendo /=.
case: Bool.bool_dec => Hf_gh; last first.
  rewrite comp_fendo_err //= => Hfg_h.
  elim: Hf_gh; apply/disjointP => i i_f.
  rewrite mem_lens_basis mem_cat => /orP [ig|ih].
    by move/disjointP/(_ i): (Hf_g); elim.
  move/disjointP/(_ i): (Hfg_h); elim => //.
  by rewrite mem_lens_basis mem_cat i_f.
rewrite {1}/comp_fendo /=.
case: Bool.bool_dec => Hfg_h; last first.
  elim: Hfg_h; apply/disjointP => i.
  rewrite mem_lens_basis mem_cat => /orP [i_f|ig] ih.
    move/disjointP/(_ i): Hf_gh; elim => //.
    by rewrite mem_lens_basis mem_cat ih orbT.
  by move/disjointP/(_ i): (Hg_h); elim.
have Hm := esym (addnA (foc_m f) (foc_m g) (foc_m h)).
apply eq_foc_endo => /=.
- by rewrite addnA.
- have -> : lens_basis (lens_cat Hf_gh) =
            cast_lens (lens_basis (lens_cat Hfg_h)) Hm.
    apply/lens_inj/eq_filter => i.
    by rewrite !(mem_cat,mem_lens_basis,orbA).
  move: (foc_m f + (foc_m g + foc_m h))%N Hm => q Hm.
  case: q / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- case: f g h Hg_h Hf_g Hf_gh Hfg_h Hm =>
        fm fl fS fe fN [] gm gl gS ge gN [] hm hl hS he hN /=
          Hg_h Hf_g Hf_gh Hfg_h Hm.
  set lhs := _ \v _.
  set rhs := _ \v _.
  suff -> : lhs = cast_mor rhs Hm Hm.
    clear lhs; subst rhs.
    move: (fm + (gm + hm))%N Hm => q Hm.
    case: q / Hm.
    apply/eq_JMeq/morP => T v /=.
    by rewrite !tpcastE.
  apply/morP => T v /= {lhs rhs}.
  rewrite !focus_comp /= -!focusM //.
  have <- : cast_lens_ord (lens_perm_left Hf_gh) (esym Hm) =
            lens_comp (lens_perm_left Hfg_h) (lens_perm_left Hf_g).
    eq_lens. rewrite -6!map_comp.
    apply/eqP/eq_map => i /=.
    rewrite !(tnth_extract,tnth_mktuple) /= !tnth_lshift.
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hf_g))) tnth_lshift.
    congr index; apply eq_filter => j.
    by rewrite !(mem_cat,mem_lens_basis) orbA.
  have <- : cast_lens_ord
              (lens_comp (lens_perm_right Hf_gh) (lens_perm_left Hg_h))
              (esym Hm) =
            lens_comp (lens_perm_left Hfg_h) (lens_perm_right Hf_g).
    eq_lens. rewrite -7!map_comp.
    apply/eqP/eq_map => i /=.
    rewrite !(tnth_extract,tnth_mktuple) /=.
    rewrite tnth_rshift [in RHS]tnth_lshift.
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hg_h))).
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hf_g))).
    rewrite tnth_lshift tnth_rshift.
    congr index; apply eq_filter => j.
    by rewrite !(mem_cat,mem_lens_basis) orbA.
  have <- : cast_lens_ord
              (lens_comp (lens_perm_right Hf_gh) (lens_perm_right Hg_h))
              (esym Hm) =
            lens_perm_right Hfg_h.
    eq_lens. rewrite -6!map_comp.
    apply/eqP/eq_map => i /=.
    rewrite !(tnth_mktuple,tnth_ord_tuple,tnth_map) /=.
    rewrite tnth_rshift [in RHS]tnth_rshift.
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hg_h))) tnth_rshift.
    congr index; apply eq_filter => j.
    by rewrite !(mem_cat,mem_lens_basis) orbA.
  have HK := tpcastK (esym Hm); rewrite esymK in HK; apply (can_inj (HK _ _)).
  rewrite {HK} tpcastK.
  move: (fm + gm + hm)%N (esym Hm) => q {}Hm.
  case: q / Hm.
  by rewrite !tpcastE !cast_lens_ordE.
Qed.

Canonical compf_monoid := Monoid.Law comp_fendoA comp_fendo1f comp_fendof1.
Canonical compf_comoid := Monoid.ComLaw comp_fendoC.
End comoid.

Section compn_mor_disjoint.
Variable m : nat.
Definition all_disjoint (F : 'I_m -> foc_endo) :=
  forall i j, i != j -> [disjoint foc_l (F i) & foc_l (F j)].

Variable F : 'I_m -> foc_endo.
Variable P : pred 'I_m.
Hypothesis Hdisj : all_disjoint F.

Definition compn_fendo :=
  \big[comp_fendo/id_fendo]_(i < m | P i) F i.

Definition compn_mor_F := compn_mor (fendo_mor \o F) P.

Lemma compn_mor_disjoint_lem :
  compn_mor_F = fendo_mor compn_fendo /\
  foc_l compn_fendo =i
  [pred i | [exists j : 'I_m, (j < m)%N && P j && (i \in foc_l (F j))]].
Proof.
pose h := m.
rewrite -{5}/h.
rewrite /compn_mor_F /compn_fendo /compn_mor /index_enum /= -enumT.
have -> : enum 'I_m = take h (enum 'I_m).
  by rewrite -[h](size_enum_ord m) take_size.
have : (h <= m)%N by [].
elim: h => [|h IH] Hh.
  rewrite take0 !big_nil.
  split.
    apply/morP => T v.
    by rewrite /fendo_mor focusE /focus_fun /= curryK.
  move=> j. rewrite inE.
  by apply/esym/existsP => -[].
case/(_ (ltnW Hh)): IH => IHe IHl.
rewrite (take_nth (Ordinal Hh)); last by rewrite size_enum_ord.
rewrite -cats1 2!big_cat.
have Hnth : nth (Ordinal Hh) (enum 'I_m) h = Ordinal Hh.
  by apply/val_inj; rewrite {2}(_ : h = Ordinal Hh) // nth_ord_enum.
rewrite Hnth in IHe *.
case Ph: (P (Ordinal Hh)); last first.
  do 2!(rewrite (big_mkcond (r:=[:: _])) big_seq1 Ph).
  rewrite IHe /= comp_fendof1; split; first exact/morP.
  move=> i /=. rewrite IHl inE; apply eq_existsb => j.
  rewrite ltnS [in RHS]leq_eqVlt.
  case jh: (j == Ordinal Hh :> nat) => //.
  move/eqP/val_inj: jh => ->.
  by rewrite ltnn Ph.
do 2!(rewrite (big_mkcond (r:=[:: _])) big_seq1 Ph).
have Hd :
  [disjoint foc_l (\big[comp_fendo/id_fendo]_(i <- take h (enum 'I_m)| P i) F i)
   & foc_l (F (Ordinal Hh))].
  apply/disjointP => j.
  rewrite IHl inE /= => /existsP [k] /andP [kh Hjk] Hjh.
  have /Hdisj : k != Ordinal Hh.
    apply/negP => /eqP kh'.
    by rewrite kh' ltnn in kh.
  by move/disjointP/(_ j); elim.
split.
  by rewrite fendo_mor_comp // IHe.
move=> i.
rewrite foc_l_comp_fendo // !inE IHl /= !inE.
apply/esym/existsP.
case: ifPn.
  case/orP.
    case/existsP => k /andP [/andP [Hk Pk] Hjk].
    exists k. by rewrite Pk ltnS (ltnW Hk).
  move=> Hjh; exists (Ordinal Hh).
  by rewrite ltnS leqnn Ph.
move/negP => Hneg [k] /andP [/andP [Hk Pk] Hjk].
elim: Hneg; apply/orP.
move: Hk; rewrite ltnS leq_eqVlt => /orP [/eqP|] Hk; [right | left].
  rewrite /is_true -Hjk.
  congr (i \in foc_l (F _)).
  by apply/val_inj.
apply/existsP; exists k.
by rewrite Hk Pk.
Qed.

Corollary compn_mor_disjoint :
  compn_mor_F = fendo_mor compn_fendo.
Proof. by case: compn_mor_disjoint_lem. Qed.

Corollary compn_mor_lens :
  foc_l compn_fendo =i [pred i | [exists j, P j && (i \in foc_l (F j))]].
Proof.
case: compn_mor_disjoint_lem => _ H i; rewrite H /= !inE.
by apply eq_existsb => j; rewrite ltn_ord.
Qed.
End compn_mor_disjoint.
End foc_endo.
End com_ring.

Section unitary.
Variable R : rcfType.
Let C := [comRingType of R[i]].
Let Co := [lmodType C of C^o].

Local Notation mor := (mor I C).
Local Notation endo n := (mor n n).

Variable n : nat.

Hypothesis cardI_gt1 : (#|I| > 1)%N.

Lemma err_fendo_notU : ~ unitary_endo (fendo_mor (@err_fendo C n)).
Proof.
move => /(_ [ffun _ => 1%:R] [ffun _ => 1%:R]) /=.
rewrite /fendo_mor focusE /tinner /=.
under eq_bigr do rewrite !ffunE.
rewrite big1 ?mulr0 //.
under eq_bigr do (rewrite !ffunE conjc_nat mulr1).
rewrite big_const card_tuple /=.
have := ltn_expl (m:=#|I|) n => /(_ cardI_gt1) Hn.
rewrite iter_addr_0 => /esym /eqP; apply/negP.
have Hn' : (0 < #|I|^n)%N by apply/leq_ltn_trans/Hn.
have : (0:C) < 1 *+ #|I| ^ n by rewrite pmulrn_lgt0.
exact/lt0r_neq0.
Qed.

Variables (m : nat) (F : 'I_m -> foc_endo C n) (P : pred 'I_m).
Hypothesis Hdisj : all_disjoint F.
Hypothesis FU : forall i, unitary_endo (F i).

Lemma compn_mor_FU : unitary_endo (compn_mor_F F P).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. exact/unitary_focus/FU/foc_n.
Qed.

Lemma compn_fendo_unitary : unitary_endo (compn_fendo F P).
Proof.
suff: unitary_endo (compn_fendo F P) \/ compn_fendo F P = err_fendo C n.
  case => //.
  move/(f_equal (@fendo_mor C n)).
  rewrite -compn_mor_disjoint // => Herr.
  elimtype False; move: compn_mor_FU.
  rewrite Herr. exact: err_fendo_notU.
rewrite /compn_fendo.
apply big_ind.
- left; exact: idmorU.
- move=> f g [] Hf; last by right; rewrite Hf comp_fendoef.
  case=> Hg; last by right; rewrite Hg comp_fendoC comp_fendoef.
  rewrite/comp_fendo.
  case: Bool.bool_dec => Hdisj' /=.
  + left. apply/unitary_comp/unitary_focus => //; last exact/foc_n.
    apply/unitary_focus => //; exact/foc_n.
  + by right.
- move=> i _ /=; left; exact/FU.
Qed.
End unitary.

End endo_monoid.
