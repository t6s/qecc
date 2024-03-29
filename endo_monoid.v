Require Reals.
From mathcomp Require Import all_ssreflect all_algebra complex.
From HB Require Import structures.
Require Import lens lens_tactics dpower unitary.
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
Local Notation "T '^^' n" := (dpower I n T).

Section com_ring.
Variable R : comRingType.

Local Notation mor m n := (mor I R m n).
Local Notation endo n := (mor n n).

Lemma MorP m n (f g : mor m n) : morf f = morf g -> f = g.
Proof.
case: f g => ff fN [gf gN] /= fg.
case: gf / fg gN => gN; exact/f_equal/proof_irrelevance.
Qed.

Lemma LinP (T1 T2 : lmodType R) (f g : {linear T1 -> T2}) :
  f =1 g -> f = g.
Proof.
move/functional_extensionality.
case: f => /= f [[Hf1] [Hf2]] /=.
case: g => /= g [[Hg1] [Hg2]] /= fg.
subst g.
have -> : Hf1 = Hg1 by apply/proof_irrelevance.
congr (_ _).
congr (_ _).
congr (_ _).
exact/proof_irrelevance.
Qed.

Lemma morP : forall m n (f g : mor m n), f =e g <-> f = g.
Proof.
split => [fg | -> //].
apply/MorP/functional_extensionality_dep => T.
apply/LinP => x.
by rewrite fg.
Qed.

Section mor_monoid.
Variable n : nat.

Lemma comp_mor1f (f : endo n) : idmor I R n \v f = f.
Proof. by apply/morP. Qed.
Lemma comp_morf1 (f : endo n) : f \v idmor I R n = f.
Proof. by apply/morP . Qed.
Lemma comp_morA' : associative (@comp_mor I R n n n).
Proof. move=> f g h; apply/morP/comp_morA. Qed.
HB.instance Definition _ :=
  Monoid.isLaw.Build (endo n) (idmor I R n) (@comp_mor I R n n n)
    comp_morA' comp_mor1f comp_morf1.

Definition compn_mor m (F : 'I_n -> endo m) (P : pred 'I_n) :=
  \big[@comp_mor I R m m m/idmor I R m]_(i < n | P i) F i.
End mor_monoid.

Lemma focus_compn_mor n m p (l : lens p m) (F : 'I_n -> endo m) P :
  focus l (compn_mor F P) = compn_mor (fun i => focus l (F i)) P.
Proof.
rewrite /compn_mor (big_morph _ (id1:=idmor I R p) (op1:=comp_mor(s:=p))) //.
- move=> x y. exact/morP/focus_comp.
- exact/morP/focus_idmor.
Qed.

Section foc_endo.
Variable n : nat.
Record foc_endo : Type :=
  mkFoc { foc_m : nat; foc_l : lens n foc_m; foc_s : lens_sorted foc_l;
          foc_e :> endo foc_m }.

Definition fendo_mor f := focus (foc_l f) f.

Section mkFendo.
Variables (m : nat) (l : lens n m) (f : endo m).
Definition mkFendo :=
  {| foc_s := lens_sorted_basis l; foc_e := focus (lens_perm l) f |}.

Lemma mkFendoE : fendo_mor mkFendo = focus l f.
Proof. by apply/morP => T v; rewrite -focusM // lens_basis_perm. Qed.
End mkFendo.

Section null.
Variables (p q : nat) (T : lmodType R).
Definition null_fun : T^^p -> T^^q := fun => 0.
Lemma null_lin : linear null_fun.
Proof. move=> x y z; by rewrite scaler0 add0r. Qed.
HB.instance Definition _ := GRing.isLinear.Build _ _ _ _ _ null_lin.
End null.

Definition nullmorlin p q : morlin _ _ p q := @null_fun p q.
Lemma nullmorN p q : naturality (nullmorlin p q).
Proof. by move=> T1 T2 h v; apply/ffunP => vi; rewrite !ffunE linearE. Qed.
Definition nullmor p q : mor p q := Mor (@nullmorN p q).

Section comoid.
Definition id_fendo := mkFoc (lens_sorted_empty n) (idmor I R 0).
Definition err_fendo := mkFoc (lens_sorted_id n) (nullmor n n).

Lemma fendo_mor_id : fendo_mor id_fendo = idmor I R n.
Proof. by apply/morP => T v; rewrite focusE /=curryK. Qed.

Lemma fendo_mor_err : fendo_mor err_fendo = nullmor n n.
Proof. by apply/morP => T v; apply/ffunP => vi; rewrite focusE /= !ffunE. Qed.

Section comp_fendo.
Definition comp_fendo (f g : foc_endo) :=
  if Bool.bool_dec [disjoint foc_l f & foc_l g] true is left H then
    mkFoc (lens_sorted_basis (lens_cat H))
          (focus (lens_perm_left H) f \v focus (lens_perm_right H) g)
  else err_fendo.

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
rewrite /comp_fendo /=.
case: Bool.bool_dec => H /=; last contradiction.
rewrite focus_comp /= -!focusM; try exact/foc_n.
by rewrite lens_perm_leftE lens_perm_rightE -lens_comp_left -lens_comp_right.
Qed.
End comp_fendo.

Lemma eq_foc_endo (f g : foc_endo) (H : foc_m f = foc_m g) :
  JMeq (foc_l f) (foc_l g) -> JMeq (foc_e f) (foc_e g) -> f = g.
Proof.
case: f g H => f_m f_l f_s f_e [] g_m g_l g_s g_e /= H.
move: f_l g_l f_e g_e f_s g_s.
case: g_m / H => f_l g_l f_e g_e f_s g_s Hl He.
move: f_s g_s.
have := JMeq_eq Hl => Hl'.
have := JMeq_eq He => He'.
subst => f_s g_s.
by rewrite (eq_irrelevance f_s g_s).
Qed.

Lemma eq_JMeq A (x y : A) : x = y -> JMeq x y.
Proof. by move=> H; subst. Qed.

Lemma focus_left_idmor p q :
  focus (lens_left p q) (idmor I R p) = idmor I R (p + q).
Proof. by apply/morP => T v; rewrite /= focusE /= curryK. Qed.

Lemma focus_right_idmor p q :
  focus (lens_right p q) (idmor I R q) = idmor I R (p + q).
Proof. by apply/morP => T v; rewrite /= focusE /= curryK. Qed.

Lemma focus_lens_right0 fm (f : endo fm) (l : lens n fm) :
  focus (lens_right 0 fm) f = f.
Proof.
apply/morP => T v /=.
rewrite -[LHS](focusI dI) -focusM //.
have Heid : [disjoint lens_empty fm & lens_id fm] by rewrite disjoint_has.
have -> : lens_id (0 + fm) = lens_cat Heid by eq_lens.
by rewrite -lens_comp_right focusI.
Qed.

Lemma comp_fendo1f (f : foc_endo) : comp_fendo id_fendo f = f.
Proof.
case: f => fm l Sl f.
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
  lens_perm_left H = cast_lens_ord Hm (lens_perm_right H').
Proof.
eq_lens; apply/eqP.
rewrite -[RHS]map_comp [RHS](@eq_map _ _ _ (@nat_of_ord _)) //.
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
case: f g H H' => f_m f_l f_s f_e [] g_m g_l g_s g_e /= H H'.
have Hm : (g_m + f_m = f_m + g_m)%N by rewrite addnC.
apply eq_foc_endo => //=.
- have -> : lens_basis (lens_cat H) =
            cast_lens Hm (lens_basis (lens_cat H')).
    apply/lens_inj/eq_filter => /= i.
    by rewrite !mem_cat orbC.
  case: _ / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- rewrite lens_perm_left_right.
  have -> : lens_perm_right H = cast_lens_ord Hm (lens_perm_left H').
    rewrite (lens_perm_left_right  H' H (esym Hm)).
    by eq_lens; apply/eqP; rewrite -!map_comp /=; apply eq_map.
  case: _ / Hm; apply eq_JMeq.
  apply/morP => T v.
  by rewrite !cast_lens_ordE focusC // disjoint_sym lens_perm_disjoint.
Qed.
    
Lemma comp_fendof1 (f : foc_endo) : comp_fendo f id_fendo = f.
Proof. by rewrite comp_fendoC comp_fendo1f. Qed.

Lemma comp_fendoef (f : foc_endo) : comp_fendo err_fendo f = err_fendo.
Proof.
rewrite /comp_fendo /=.
case: Bool.bool_dec => //.
case: f => -[|m] l Sl e /= H; last first.
  have [] : False; case: l {Sl e} H => -[] [] //= a t Hsz Hu.
  by rewrite disjoint_sym disjoint_has /= mem_enum.
have Hn : (n = n + 0)%N by rewrite addn0.
apply eq_foc_endo => //=.
- have -> : lens_basis (lens_cat H) = cast_lens Hn (lens_id n).
    apply/lens_inj; rewrite -[RHS]enum_filterP.
    by apply eq_filter => i; rewrite mem_cat mem_lens_full.
  case: _ / Hn; apply eq_JMeq.
  by rewrite cast_lensE.
- rewrite (_ : _ \v _ = nullmor (n+0) (n+0)); last first.
    by apply/morP => T v; apply/ffunP => vi; rewrite /= !focusE !ffunE.
  by case: _ / Hn.
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
            cast_lens Hm (lens_basis (lens_cat Hfg_h)).
    apply/lens_inj/eq_filter => i.
    by rewrite !(mem_cat,mem_lens_basis,orbA).
  case: _ / Hm; apply eq_JMeq.
  by rewrite cast_lensE.
- case: f g h Hg_h Hf_g Hf_gh Hfg_h Hm =>
        fm fl fS fe [] gm gl gS ge [] hm hl hS he /=
          Hg_h Hf_g Hf_gh Hfg_h Hm.
  set lhs := _ \v _.
  set rhs := _ \v _.
  suff -> : lhs = cast_mor Hm Hm rhs.
    clear lhs; subst rhs.
    case: _ / Hm.
    apply/eq_JMeq/morP => T v /=.
    by rewrite !dpcastE.
  apply/morP => T v /= {lhs rhs}.
  rewrite !focus_comp /= -!focusM //.
  have <- : cast_lens_ord (esym Hm) (lens_perm_left Hf_gh) =
            lens_comp (lens_perm_left Hfg_h) (lens_perm_left Hf_g).
    eq_lens. rewrite -6!map_comp.
    apply/eqP/eq_map => i /=.
    rewrite !(tnth_extract,tnth_mktuple) /= !tnth_lshift.
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hf_g))) tnth_lshift.
    congr index; apply eq_filter => j.
    by rewrite !(mem_cat,mem_lens_basis) orbA.
  have <- : cast_lens_ord (esym Hm)
              (lens_comp (lens_perm_right Hf_gh) (lens_perm_left Hg_h)) =
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
  have <- : cast_lens_ord (esym Hm)
              (lens_comp (lens_perm_right Hf_gh) (lens_perm_right Hg_h)) =
            lens_perm_right Hfg_h.
    eq_lens. rewrite -6!map_comp.
    apply/eqP/eq_map => i /=.
    rewrite !(tnth_mktuple,tnth_ord_tuple,tnth_map) /=.
    rewrite tnth_rshift [in RHS]tnth_rshift.
    rewrite (tnth_lens_index (l:=lens_basis (lens_cat Hg_h))) tnth_rshift.
    congr index; apply eq_filter => j.
    by rewrite !(mem_cat,mem_lens_basis) orbA.
  have HK := dpcastK (esym Hm); rewrite esymK in HK; apply (can_inj (HK _ _)).
  rewrite {HK} dpcastK.
  case: _ / (esym Hm).
  by rewrite !dpcastE !cast_lens_ordE.
Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build foc_endo id_fendo comp_fendo
    comp_fendoA comp_fendoC comp_fendo1f.

Lemma disjoint_comp_fendo m (l : lens n m) g h :
  [disjoint l & foc_l g] -> [disjoint l & foc_l h] ->
  [disjoint foc_l g & foc_l h] -> [disjoint l & foc_l (comp_fendo g h)].
Proof.
move=> lg lh gh; rewrite /comp_fendo /=.
case: Bool.bool_dec => //= H.
rewrite disjoint_sym disjoint_has -all_predC.
apply/allP => i.
rewrite mem_lens_basis mem_lensE /= mem_cat => /orP[] Hi.
- by move: lg; rewrite disjoint_sym disjoint_has -all_predC => /allP /(_ _ Hi).
- by move: lh; rewrite disjoint_sym disjoint_has -all_predC => /allP /(_ _ Hi).
Qed.
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
  split. by rewrite fendo_mor_id.
  move=> j; rewrite inE; by apply/esym/existsP => -[].
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
Let C : comRingType := R[i].
Let Co : lmodType C := C^o.

Local Notation mor := (mor I C).
Local Notation endo n := (mor n n).

Variable n : nat.

Hypothesis cardI_gt1 : (#|I| > 1)%N.

Lemma err_fendo_notU : ~ unitary_mor (fendo_mor (@err_fendo C n)).
Proof.
move => /(_ [ffun _ => 1%:R] [ffun _ => 1%:R]).
rewrite fendo_mor_err /tinner /=.
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
Hypothesis FU : forall i, unitary_mor (F i).

Lemma compn_mor_FU : unitary_mor (compn_mor_F F P).
Proof.
apply: big_ind.
- exact: idmorU.
- exact: unitary_comp.
- move=> i _. exact/unitary_focus/FU.
Qed.

Lemma compn_fendo_unitary : unitary_mor (compn_fendo F P).
Proof.
suff: unitary_mor (compn_fendo F P) \/ compn_fendo F P = err_fendo C n.
  case => //.
  move/(f_equal (@fendo_mor C n)).
  rewrite -compn_mor_disjoint // => Herr.
  have [] : False; move: compn_mor_FU.
  rewrite Herr. exact: err_fendo_notU.
rewrite /compn_fendo.
apply big_ind.
- left; exact: idmorU.
- move=> f g [] Hf; last by right; rewrite Hf comp_fendoef.
  case=> Hg; last by right; rewrite Hg comp_fendoC comp_fendoef.
  rewrite/comp_fendo.
  case: Bool.bool_dec => Hdisj' /=.
  + left. apply/unitary_comp/unitary_focus => //.
    exact/unitary_focus.
  + by right.
- move=> i _ /=; left; exact/FU.
Qed.
End unitary.

End endo_monoid.
