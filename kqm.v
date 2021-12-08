(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower qexamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section move_to_somewhere.
Variables (I : finType) (dI : I) (R : comRingType).

Definition idmorfun n : morfun I R n n := fun _ x => x.
Lemma idmor_linear n T : linear (@idmorfun n T).
Proof. by []. Qed.
Definition idmor n : mor I R n n := fun T => Linear (@idmor_linear n T).

Lemma congr_comp_mor r q s (phi phi' : mor I R q s) (psi psi' : mor I R r q) :
  phi =e phi' -> psi =e psi' -> phi \v psi =e phi' \v psi'.
Proof.
move=> Hphi Hpsi T x /=.
move: (Hpsi T x) ->.
by move: (Hphi T (psi' T x)).
Qed.

Lemma uncurry_inj (T : lmodType R) n m (l : lens n m)
      (x y : tpower I m (tpower I (n - m) T)) :
  uncurry l x = uncurry l y -> x = y.
Proof. by apply/can_inj/uncurryK. Qed.

Lemma curry_inj (T : lmodType R) n m (l : lens n m) (x y : tpower I n T) :
  curry dI l x = curry dI l y -> x = y.
Proof. by apply/can_inj/curryK. Qed.
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

Section cap_cup.
Variables (n : nat) (l : lens n 2).
Definition curry0 (L : lmodType R) (v : L) : tpower I 0 L := [ffun _ => v].
Definition curryn0 n (L : lmodType R) (v : tpower I n L)
  : tpower I n (tpower I 0 L) := [ffun vi => [ffun _ => v vi]].
Definition uncurry0 (L : lmodType R) (v : tpower I 0 L) : L :=
  v [tuple of nil].

Section renaming.
Local Notation pv_of_coef := curry0.
Local Notation coef_of_pv := uncurry0.
Local Notation lift_pv_of_coef := curryn0.
Lemma lift_pv_of_coefE  L :
  @lift_pv_of_coef n L = @map_tpower I n _ _ (@pv_of_coef L).
Proof.
rewrite /lift_pv_of_coef /map_tpower.
rewrite boolp.funeqE=> v.
apply ffunP=> i.
by rewrite !ffunE.
Qed.
End renaming.

Lemma curry0_is_linear T : linear (@curry0 T).
Proof. move=> x y z. apply/ffunP => vi. by rewrite !ffunE. Qed.
Lemma uncurry0_is_linear T : linear (@uncurry0 T).
Proof. move=> x y z. by rewrite /uncurry0 !ffunE. Qed.

Definition cap_fun : morfun I R n (n-2) :=
  fun T : lmodType R =>
    uncurry0 (L:=_) \o
    tsmor (curry0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry l (T:=T).

Definition cup_fun : morfun I R (n-2) n :=
  fun T : lmodType R =>
    uncurry l \o
    tsmor (curryn0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry0 (L:=_).

Definition cap_fun2 (M : tsquare 1) T :=
 tsmor (curry0 (uncurry (lens_left 1 1) M)) T.

Definition inner_prod T := uncurry0 (L:= _) \o cap_fun2 (id_tsquare _ _ _) T.

Lemma cap_is_linear T : linear (@cap_fun T).
Proof.
move=> x y z.
by rewrite /cap_fun /= curry_is_linear tsmor_is_linear uncurry0_is_linear.
Qed.

Lemma cup_is_linear T : linear (@cup_fun T).
Proof.
move=> x y z.
by rewrite /cup_fun /= curry0_is_linear tsmor_is_linear uncurry_is_linear.
Qed.

Definition cap : mor I R n (n-2) :=
  fun T : lmodType R => Linear (@cap_is_linear T).
Definition cup : mor I R (n-2) n :=
  fun T : lmodType R => Linear (@cup_is_linear T).
End cap_cup.

Lemma sum_scaler_cond A (L : lmodType R)(r : seq A)(P Q : pred A)(F : A -> L) :
  (\sum_(i <- r | P i) (Q i)%:R *: F i = \sum_(i <- r | P i && Q i) F i)%R.
Proof.
rewrite big_mkcondr /=; apply eq_bigr => i _.
case: ifP; by rewrite (scale1r,scale0r).
Qed.

Ltac eq_lens :=
  apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.

Lemma transpose_cup (M : tsquare 1) :
  focus [lens 0] (tsmor M) \v cup (n:=2) [lens 0; 1] =e
  focus [lens 1] (tsmor (transpose_tsquare M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /cup_fun !focusE /=.
do! rewrite !(ffunE,sum_ffunE,sum_enum_indices) /= !addr0 !ffunE.
have -> : [lens 0; 1] = lens_id 2 by eq_lens.
rewrite !extract_lens_id.
have -> : lens_left 1 1 = [lens 0] by eq_lens.
rewrite !extract_merge !extract_lothers_merge.
have -> : lothers [lens 0] = [lens 1] by eq_lens.
rewrite !extract_merge.
have l10 : lothers [lens 1] = [lens 0] by eq_lens.
rewrite -l10 !(extract_lothers_merge _ [lens 1]) l10.
have -> : lothers (lens_id 2) = lens_empty 2.
  by eq_lens; rewrite /= !ifF // -topredE /= enum_ordinalE.
rewrite !extract_lens_empty.
have := mem_enum_indices (extract [lens 0] vi).
have := mem_enum_indices (extract [lens 1] vi).
rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> /=;
by rewrite !(add0r,addr0,scale0r,scaler0,scale1r).
Qed.

Lemma straighten : cap [lens 1; 2] \v cup [lens 0; 1] =e idmor 1.
Proof.
move=> T /= v.
rewrite /cap_fun /cup_fun.
(*
Check (uncurry0 (L:=ffun_lmodType (tuple_finType (1 + 2 - 2) I) T) \o
       tsmor (curry0 (uncurry (lens_left 1 1) (id_tsquare I R 1)))
         (ffun_lmodType (tuple_finType (1 + 2 - 2) I) T)).

rewrite (lock tsmor).
rewrite /curry0 /uncurry0 /=.
rewrite -lock.
Check tsmor [ffun=> uncurry (lens_left 1 1) (id_tsquare I R 1)] (ffun_lmodType (tuple_finType (1 + 2 - 2) I) T) = uncurry_mor _ _ (lens_left 1 1).

rewrite /uncurry0 /curry /uncurry /curry0 /idmorfun /=.
rewrite /tsmor_fun /=.
apply ffunP=> /= vi.
rewrite 2!ffunE.
rewrite sum_enum_indices /= !ffunE.
*)
Abort.

Lemma transpose_focus (M : tsquare 1) :
  tsmor (transpose_tsquare M) =e
  cap [lens 1; 2] \v focus [lens 1] (tsmor M) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /cap_fun /cup_fun !ffunE /uncurry0 /curry0 /= !ffunE sum_ffunE.
under eq_bigr do rewrite ffunE.
symmetry.
under eq_bigr do rewrite !ffunE.
rewrite sum_scaler_cond /=.
rewrite
  (reindex_onto (fun v => [tuple tnth v ord0; tnth v ord0]) (fun v : 2.-tuple _ => [tuple tnth v ord0])) /=;
  last first.
  move=> vj.
  rewrite eq_tuple /= => /eqP.
  rewrite /others /lens_left !enum_ordinalE /= -!topredE /= !enum_ordinalE /=.
  case => H1.
  apply eq_from_tnth => -[] [|[]] // Hi; rewrite (tnth_nth (tnth vj ord0)) /=;
    rewrite (tnth_nth (tnth vj ord0)) /=.
  - rewrite /=. congr tnth. exact: val_inj.
  - have {1}-> : ord0 = lshift 1 ord0 :> 'I_(1+1) by apply: val_inj.
    rewrite H1; congr tnth; exact: val_inj.
apply eq_big => vj.
  apply/andP; split.
  - rewrite eq_tuple; apply/eqP.
    rewrite /= /others /lens_left !enum_ordinalE /=.
    by rewrite -!topredE /= !enum_ordinalE.
  - apply/eqP/eq_from_tnth => j.
    by rewrite !ord1 (tnth_nth (tnth vj ord0)) /= (tnth_nth (tnth vj ord0)).
move=> _.
rewrite focusE /=.
rewrite !ffunE.
rewrite sum_enum_indices /=.
have {1 3}-> : [lens 1] = lens_comp [lens 1;2] [lens 0].
  move=> n. apply/val_inj/eq_from_tnth => i /=.
  by rewrite ord1 (tnth_nth ord0) ![RHS](tnth_nth ord0).
rewrite extract_comp extract_merge addr0.
Abort.

Definition id_tsquare' n : tpower I n (tpower I (n + n - n) R^o).
rewrite addKn.
exact (id_tsquare I R n).
Defined.

(*
Lemma transpose_focus n (M : tsquare n) T :
  tsmor (transpose M) T =1
  uncurry (lens_left 0 n) \o
  tsmor (curry0 (uncurry (lens_left n n) (id_tsquare I R n))) _ \o
  @curry0 _ \o
  focus (lens_right n (n+n)) (focus (lens_left n n) (tsmor M)) _ \o
  uncurry (lens_left (n+n) n) \o
  tsmor (curry (lens_left (n+n) 0) (uncurry (lens_left n n) (id_tsquare I R n))) _ \o
  curry (lens_left 0 n).
Proof.
move=> v /=.
apply/ffunP => vi /=.
rewrite !ffunE /= sum_ffunE.
Abort.
*)

End transpose.
