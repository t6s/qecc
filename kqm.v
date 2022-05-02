(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower qexamples.

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
Variables (n : nat) (l : lens n 2).

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
End cap_cup.

Lemma extract_rev A n m (l1 l2 : lens n m) (v : n.-tuple A) :
  rev l1 = l2 -> [tuple of rev (extract l1 v)] = extract l2 v.
Proof.
case: m l1 l2 => [|m] l1 l2 Hrev.
  rewrite !extract_lens_empty; exact/val_inj.
apply/val_inj/eq_from_nth' => /=.
  by rewrite size_rev !size_tuple.
move=> a i.
rewrite size_rev => Hi.
rewrite nth_rev //= size_map size_tuple -Hrev.
rewrite (nth_map (tnth l1 ord0)).
  rewrite size_map in Hi.
  rewrite -[X in X - i.+1](size_tuple l1) -nth_rev //.
  by rewrite -(nth_map _ a) // size_rev.
by rewrite size_tuple ltn_subrL.
Qed.

Ltac eq_lens :=
  apply/val_inj/eqP; rewrite ?eq_ord_tuple /= /others /= ?enum_ordinalE.

Lemma lens_left_1 n : lens_left 1 n = [lens 0].
Proof. by eq_lens. Qed.

Lemma lens_right_1 n : lens_right n 1 = [lens n].
Proof. by eq_lens; rewrite /= addnOK. Qed.

Lemma cup_sym n (l1 l2 : lens n 2) :
  rev l1 = l2 -> cup l1 =e cup l2.
Proof.
move=> Hrev T v.
apply/ffunP => vi.
rewrite !(ffunE,tsmorE) !cast_tupleE !(big_pred1 [tuple]); try by case => -[].
rewrite !ffunE.
congr (_ *: v (extract _ vi))%R.
- rewrite -(extract_rev _ Hrev) => {l2 Hrev}.
  case: (extract l1 vi) => -[|a [|b []]] //= Hl1.
  rewrite (lens_eq_cast (lothers_left 1 1)) cast_lensE.
  rewrite lens_left_1 lens_right_1.
  by rewrite !eq_ord_tuple /= !(tnth_nth a) /= eq_sym.
- apply/val_inj/val_inj/eq_filter => i.
  by rewrite !mem_lensE !memtE /= -Hrev mem_rev.
Qed.

Lemma sum_scaler_cond A (L : lmodType R)(r : seq A)(P Q : pred A)(F : A -> L) :
  (\sum_(i <- r | P i) (Q i)%:R *: F i = \sum_(i <- r | P i && Q i) F i)%R.
Proof.
rewrite big_mkcondr /=; apply eq_bigr => i _.
case: ifP; by rewrite (scale1r,scale0r).
Qed.

Lemma transpose_cup (M : tsquare 1) :
  focus [lens 0] (tsmor M) \v cup (n:=2) [lens 0; 1] =e
  focus [lens 1] (tsmor (transpose_tsquare M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /cup_fun !focusE /=.
do! rewrite !(tsmorE,ffunE,sum_ffunE,sum_enum_indices) /= !addr0 !ffunE.
have -> : [lens 0; 1] = lens_id 2 by eq_lens.
rewrite !extract_lens_id.
rewrite lens_left_1 !extract_merge !extract_lothers_merge.
have -> : lothers [lens 0] = [lens 1] by eq_lens.
rewrite !extract_merge.
have l10 : lothers [lens 1] = [lens 0] by eq_lens.
rewrite -l10 !(extract_lothers_merge _ [lens 1]) l10.
rewrite (lens_eq_cast (lothers_id 2)) cast_lensE !extract_lens_empty.
have := mem_enum_indices (extract [lens 0] vi).
have := mem_enum_indices (extract [lens 1] vi).
rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> /=;
by rewrite !(add0r,addr0,scale0r,scaler0,scale1r).
Qed.

Lemma cat_2tuple A (x y : A) : [tuple of [tuple x]++[tuple y]] =  [tuple x; y].
Proof. exact/val_inj. Qed.

Lemma straighten : cap [lens 1; 2] \v cup [lens 0; 1] =e idmor 1.
Proof.
move=> T /= v.
rewrite /cap_fun /cup_fun.
apply/ffunP => t /=.
rewrite /uncurry0 /inner_prod /inner_coprod /M_inner_prod /M_inner_coprod.
rewrite map_tpcastE tsmorE sum_enum_indices /= !ffunE /=.
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

Lemma transpose_focus (M : tsquare 1) :
  tsmor (transpose_tsquare M) =e
  cap [lens 1; 2] \v focus [lens 1] (tsmor M) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
have -> : [lens 1] = lens_comp (lens_left 2 1) [lens 1].
  by eq_lens; rewrite tnth_mktuple.
rewrite focusM; last by apply/naturalityP; eexists.
rewrite [in RHS]focusE /= /focus_fun.
have -> : cup_fun (n:=3) [lens 0; 1] v =
  uncurry (lens_left 2 1) (cup_fun (n:=2) [lens 0; 1] (curry0 _ v)).
  admit.
rewrite uncurryK.
have /= := transpose_cup (transpose_tsquare M) (curry0 I v).
rewrite transpose_tsquare_involutive => <-.
have<- := uncurryK dI (lens_left 2 1) (cup_fun (n:=2) [lens 0; 1] (curry0 _ v)).
set mycup := uncurry _ (cup_fun _ _).
have := focusM dI (lens_left 2 1) [lens 0] (tr:=tsmor (transpose_tsquare M)) _ mycup.
rewrite [in focus (lens_left 2 1) _ _ _]focusE /= /focus_fun => <-.
have <- : [lens 0] = lens_comp (lens_left 2 1) [lens 0]
  by eq_lens; rewrite tnth_mktuple.
Abort.

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
