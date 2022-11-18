(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section move_to_somewhere.
Variables (I : finType) (R : comRingType).
Definition idmor n : mor I R n n := fun T => GRing.idfun_linear _.

Lemma congr_comp_mor r q s (phi phi' : mor I R q s) (psi psi' : mor I R r q) :
  phi =e phi' -> psi =e psi' -> phi \v psi =e phi' \v psi'.
Proof. by move=> Hphi Hpsi T x /=; rewrite Hpsi Hphi. Qed.

Variables (dI : I) (T : lmodType R) (n m : nat) (l : lens n m).
Definition uncurry_inj := can_inj (uncurryK dI l (T:=T)).
Definition curry_inj := can_inj (curryK dI l (T:=T)).
End move_to_somewhere.

Section transpose.

Variables (R : comRingType).
Let I := [finType of 'I_2].
Let dI : I := ord0.

Notation idmor n := (idmor I n).
Notation tsquare m := (tmatrix I R m m).
Notation endo n := (mor I R n n).

Notation focus := (focus dI).
Notation curry := (curry dI).

Local Definition sum_enum_indices := sum_enum_indices uniq_enum2 mem_enum2.
Local Definition mem_enum_indices := mem_enum_indices mem_enum2.
Local Definition forall_indicesP := forall_indicesP mem_enum2.

Section cap_cup.
Variables (n : nat) (l : lens (2 + n) 2).

Definition cap := asym_focus dI (R:=R) (p:=0) l (lens_empty n) (inner_prod I 1).
Definition cup :=
  asym_focus dI (R:=R) (m:=0) (lens_empty n) l (inner_coprod I 1).
(*
Definition cap_fun : morfun I R n (n-2) :=
  fun T : lmodType R =>
    uncurry0 (T:=_) \o inner_prod I 1 _ \o curry l (T:=T).

Definition cup_fun : morfun I R (n-2) n :=
  fun T : lmodType R =>
    uncurry l \o inner_coprod I 1 _ \o curry0 I (T:=_).

Lemma cap_is_linear T : linear (@cap_fun T).
Proof.
move=> x y z.
by rewrite /cap_fun /= curry_is_linear linearPZ uncurry0_is_linear.
Qed.

Lemma cup_is_linear T : linear (@cup_fun T).
Proof.
move=> x y z.
by rewrite /cup_fun /= curry0_is_linear linearPZ uncurry_is_linear.
Qed.

Definition cap : mor I R n (n-2) :=
  fun T : lmodType R => Linear (@cap_is_linear T).
Definition cup : mor I R (n-2) n :=
  fun T : lmodType R => Linear (@cup_is_linear T).
*)
End cap_cup.

Lemma extract_rev A n m (l1 l2 : lens n m) (v : n.-tuple A) :
  rev l1 = l2 -> [tuple of rev (extract l1 v)] = extract l2 v.
Proof. by move=> Hrev; apply/val_inj; rewrite /= -map_rev Hrev. Qed.

Ltac eq_lens :=
  apply/val_inj/eqP; rewrite ?eq_ord_tuple /= /others /= ?enum_ordinalE.

Lemma lens_left_1 n : lens_left 1 n = [lens 0].
Proof. by eq_lens. Qed.

Lemma lens_right_1 n : lens_right n 1 = [lens n].
Proof. by eq_lens; rewrite /= addnOK. Qed.

Lemma cup_sym n (l1 l2 : lens (2+n) 2) :
  rev l1 = l2 -> cup l1 =e cup l2.
Proof.
move=> Hrev T v.
apply/ffunP => vi.
rewrite !(ffunE,tsmorE) !cast_tupleE !(big_pred1 [tuple]); try by case => -[].
rewrite !ffunE.
rewrite -!extract_comp.
have Hl1 : lens_comp l1 (lens_left 1 1) = lens_comp l2 (lothers(lens_left 1 1)).
  apply/val_inj/val_inj => /=.
  move: (lothers_left 1 1) => /= ->.
  rewrite !enum_ordinalE /= !(tnth_nth ord0) /=.
  by rewrite -Hrev nth_rev // size_tuple.
have Hl2 : lens_comp l2 (lens_left 1 1) = lens_comp l1 (lothers(lens_left 1 1)).
  apply/val_inj/val_inj => /=.
  move: (lothers_left 1 1) => /= ->.
  rewrite !enum_ordinalE /= !(tnth_nth ord0) /=.
  by rewrite -Hrev nth_rev // size_tuple.
rewrite -Hl1 -Hl2 [in RHS]eq_sym.
case H: (_ == _); last by rewrite !scale0r.
rewrite !scale1r !merge_indices_empty.
do 3!f_equal.
apply/val_inj/val_inj/eq_filter => /= i.
by rewrite !mem_lensE !memtE -Hrev mem_rev.
Qed.

Lemma sum_scaler_cond A (L : lmodType R)(r : seq A)(P Q : pred A)(F : A -> L) :
  (\sum_(i <- r | P i) (Q i)%:R *: F i = \sum_(i <- r | P i && Q i) F i)%R.
Proof.
rewrite big_mkcondr /=; apply eq_bigr => i _.
case: ifP; by rewrite (scale1r,scale0r).
Qed.

Lemma transpose_cup (M : tsquare 1) :
  focus [lens 0] (tsmor M) \v cup (n:=1) [lens 0; 1] =e
  focus [lens 1] (tsmor (transpose_tsquare M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /asym_focus_fun !focusE /= /focus_fun.
do! rewrite !(tsmorE,ffunE,sum_ffunE,sum_enum_indices) /= !addr0 !ffunE.
(* have -> : [lens 0; 1] = lens_id 2 by eq_lens. *)
(* rewrite !extract_lens_id. *)
rewrite !lens_left_1. (* !extract_merge !extract_lothers_merge. *)
have -> : lothers [lens 0] = [lens 1] by eq_lens.
rewrite !cast_tupleE /=.
rewrite -!extract_comp.
have -> : lens_comp [lens 0; 1] [lens 0] = [lens 0] :> lens 3 1 by eq_lens.
have -> : lens_comp [lens 0; 1] [lens 1] = [lens 1] :> lens 3 1 by eq_lens.
rewrite !extract_merge.
rewrite !merge_indices_empty /=.
rewrite !extract_merge_disjoint.
rewrite !scalerA.
rewrite -!scalerDl.
f_equal.
have := mem_enum_indices (extract [lens 0] vi).
have := mem_enum_indices (extract [lens 1] vi).
by rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> /=;
   rewrite !(mulr0,addr0,add0r).
all: by rewrite disjoint_has //= /others enum_ordinalE.
Qed.  

Lemma cat_2tuple A (x y : A) : [tuple of [tuple x]++[tuple y]] =  [tuple x; y].
Proof. exact/val_inj. Qed.

Lemma straighten : cap [lens 1; 2] \v cup [lens 0; 1] =e idmor 1.
Proof.
move=> T /= v.
rewrite /asym_focus_fun.
apply/ffunP => t /=.
rewrite /inner_prod /inner_coprod /M_inner_prod /M_inner_coprod.
rewrite {1}/uncurry !ffunE /= !tsmorE.
rewrite sum_enum_indices /= !ffunE /=.
rewrite -!cat_2tuple !extract_lens_left.
rewrite !(extract_eq_cast (lothers_left 1 1)) !extract_lens_right /= !linE.
rewrite !tsmorE !sum_enum_indices /= !ffunE /= !addr0.
apply/eqP; move: t; apply/forall_indicesP.
rewrite /= andbT; apply/andP.
(* brute force *)
rewrite !eq_ord_tuple /= /tnth /= /tnth /= /others.
rewrite /in_mem /mem /= !enum_ordinalE /= !linE.
split; apply/eqP/f_equal/eqP;
  by rewrite eq_ord_tuple /= /tnth /= /others !enum_ordinalE.
(* incremental proof
rewrite -!extract_comp !(lens_eq_cast (lothers_left 1 1)) /=.
rewrite (_ : lens_comp _ _ = [lens 0]); last by eq_lens.
rewrite (_ : lens_comp _ _ = [lens 1]); last by eq_lens.
have -> : lothers [lens 0; 1] = [lens 2] by eq_lens.
have <- : lothers [lens 1; 2] = [lens 0] by eq_lens.
rewrite !(@extract_lothers_merge _ _ 3 2 [lens 1;2]).
rewrite -(_ : lens_comp [lens 1; 2] [lens 0] = [lens 1]); last by eq_lens.
rewrite -(_ : lens_comp [lens 1; 2] [lens 1] = [lens 2]); last by eq_lens.
rewrite !extract_comp !extract_merge /= !linE.
by split; apply/eqP; f_equal; apply/eqP; rewrite eq_ord_tuple. *)
Qed.

(*
Lemma cap_focusC n p (l1 : lens n 2) (l2 : lens (n-2) p) (tr : endo p) :
  naturality tr ->
  cap l1 \v focus (lens_comp (lothers l1) l2) tr =e
  focus l2 tr \v cap l1.
Proof.
move=> /naturalityP [M HM] T v /=.
rewrite !focusE /= /focus_fun /cap_fun !HM.
apply/ffunP => vi.
rewrite !(ffunE,sum_ffunE) /=.
rewrite /uncurry0 /=.
rewrite !(tsmorE,ffunE,sum_ffunE) /=.
Abort.
*)

Lemma comp_morA m n p q (f : mor I R m n) (g : mor I R n p) (h : mor I R p q) :
  h \v (g \v f) =e (h \v g) \v f.
Proof. by []. Qed.

Lemma comp_morE m n p (f : mor I R m n) (g : mor I R n p) T v :
 (g \v f) T v = g T (f T v).
Proof. by []. Qed.

Definition cast_mor m2 n2 m1 n1 (f : mor I R m1 n1)
           (Hm : m1 = m2) (Hn : n1 = n2) : mor I R m2 n2.
rewrite -> Hm, -> Hn in f.
exact f.
Defined.

(*
Lemma asym_focus_cup n :
  cast_mor (cup (lens_left 2 n)) (addKn _ _) (erefl _) =e
  asym_focus dI (lens_left 0 n) (lens_left 2 n)
    (cup ([lens 0; 1] : lens 2 2)).
Proof.
move=> T v /=.
rewrite /asym_focus_fun /=.
apply/ffunP => vi.
rewrite !ffunE.
rewrite /cup_fun /uncurry /curry /=.
Abort.

Lemma asym_focus_cup :
  cup (lens_left 2 1) =e
  asym_focus dI (lens_left 0 1) (lens_left 2 1)
    (cup ([lens 0; 1] : lens 2 2)).
Proof.
move=> T v /=.
rewrite /asym_focus_fun /=.
apply/ffunP => vi.
rewrite !ffunE.
f_equal; last by apply val_inj.
apply/ffunP => vj.
rewrite /inner_coprod /M_inner_coprod /= !tsmorE !ffunE /= !sum_ffunE.
apply eq_bigr => i _.
rewrite !ffunE -!extract_comp /=.
have -> : lens_comp (lens_left 2 1) [lens 0; 1] = lens_left 2 1.
  eq_lens => /=.
  by apply/eqP; do! f_equal; rewrite (tnth_nth ord0) /= enum_ordinalE.
have -> : lens_comp (lens_left 2 1) (lens_left 1 1) = [lens 0].
  by eq_lens; rewrite /mktuple /= (tnth_nth ord0) /= enum_ordinalE.
have -> : lens_comp (lens_left 2 1) (lothers (lens_left 1 1)) = [lens 1].
  eq_lens; rewrite -map_comp /= !mem_lensE !memtE /= enum_ordinalE /=.
  by rewrite (tnth_nth ord0) /= enum_ordinalE.
have -> : lens_comp (lens_left 2 1) (lothers [lens 0; 1]) = [lens] by eq_lens.
case H: (tnth vi 0%:O == tnth vi 1%:O).
  rewrite (_ : (_ == _) = true); last first.
    rewrite !eq_ord_tuple /= (eqP H). exact/eqP.
  rewrite !scale1r.
  have -> : lens_left 0 1 = lens_empty 1 by eq_lens.
  f_equal; apply/val_inj.
  by rewrite merge_indices_empty.
rewrite (_ : (_ == _) = false).
  by rewrite !scale0r.
rewrite !eq_ord_tuple /=.
apply/eqP => -[] /val_inj vi01.
by rewrite vi01 eqxx in H.
Qed.
*)

Lemma focus_empty n (f : endo n) :
  naturality f ->
  focus (lothers (lens_empty n)) (cast_mor f (esym (subn0 n)) (esym (subn0 n)))
  =e f.
Admitted.

Lemma transpose_focus (M : tsquare 1) :
  tsmor (transpose_tsquare M) =e
  cap [lens 1; 2] \v focus [lens 1] (tsmor M) \v cup [lens 0; 1].
Proof.
rewrite -{2}(transpose_tsquare_involutive M).
move=> T v.
rewrite -comp_morA comp_morE comp_morE.
move: (transpose_cup (transpose_tsquare M) v) => /= <-.
Search naturality.
have NM : naturality (tsmor (transpose_tsquare M)) by apply/naturalityP; esplit.
have NIP : naturality (inner_prod I 1 (R:=R)) by apply/naturalityP; esplit.
set mycup := asym_focus_fun dI (lens_empty 1 : lens (0+1) 0) ([lens 0; 1] : lens (2+1) 2) (inner_coprod I 1) v.
move: (asym_focusC dI ([lens 1; 2] : lens (2+1) 2) (lens_empty 1 : lens (0+1) 0) NM NIP mycup).
rewrite !cast_lensE.
have -> : lothers [lens 1; 2] = [lens 0] by eq_lens.
move => /= <-.
subst mycup.
move: (straighten v) => /= ->.
move: (focus_empty NM v) => <-.
rewrite !focusE /focus_fun /= /cast_mor /=.
have -> // : subn0 1 = erefl by apply nat_irrelevance.
Qed.

Definition idts' n : tpower I n (tpower I (n + n - n) R^o).
rewrite addKn.
exact (idts I R n).
Defined.

(*
Lemma transpose_focus n (M : tsquare n) T :
  tsmor (transpose M) T =1
  uncurry (lens_left 0 n) \o
  tsmor (curry0 (uncurry (lens_left n n) (idts I R n))) _ \o
  @curry0 _ \o
  focus (lens_right n (n+n)) (focus (lens_left n n) (tsmor M)) _ \o
  uncurry (lens_left (n+n) n) \o
  tsmor (curry (lens_left (n+n) 0) (uncurry (lens_left n n) (idts I R n))) _ \o
  curry (lens_left 0 n).
Proof.
move=> v /=.
apply/ffunP => vi /=.
rewrite !ffunE /= sum_ffunE.
Abort.
*)

End transpose.
